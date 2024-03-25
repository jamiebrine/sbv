---------------------------------------------------------------------------------
---------------------------Imports and Structures--------------------------------
---------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use head" #-}

import Control.Monad (guard)
import Control.Monad.RWS (MonadIO (liftIO), gets)
import Data.Char (isLetter)
import Data.Function (on)
import Data.List (find, intercalate, minimumBy, nub, sort, subsequences, (\\))
import Data.Time (TimeLocale (time12Fmt))
import Distribution.SPDX (LicenseId (OCCT_PL))
import Distribution.Simple (ProfDetailLevel (ProfDetailToplevelFunctions), defaultMainNoRead)
import Distribution.Simple.Command (OptDescr (BoolOpt))
import Distribution.Simple.Utils (xargs)
import GHC.Exts.Heap (GenClosure (tsoStack))
import Language.Haskell.TH (safe)
import System.Console.Haskeline
  ( InputT,
    defaultSettings,
    getInputLine,
    outputStrLn,
    runInputT,
  )
import System.Posix (ProcessStatus (Terminated))
import Text.Read (Lexeme (String))

data Term = O | V Char | Not Term | Seq [Term] | Par [Term] | Copar [Term]

type Proof = [(Term, Char)]

instance Show Term where
  show = outputTerm
  showList = outputTerms

instance Eq Term where
  (==) = (~=)
  (/=) = (/~=)

----------------------------------------------------------------------------------
---------------------------String Parsing and Outputting-------------------------
---------------------------------------------------------------------------------

-- Parses an input string as an SBV Term
parse :: String -> Term
parse x = case x of
  "O" -> O
  y : "" -> parseVar y
  '-' : xs -> parseNot (parse xs)
  '<' : xs -> parseSeq 0 [] [] xs
  '[' : xs -> parsePar 0 [] [] xs
  '(' : xs -> parseCopar 0 [] [] xs
  _ -> error "Invalid expression - invalid sequence of characters"
  where
    -- Checks that a character is a lowercase letter
    parseVar :: Char -> Term
    parseVar c
      | isLetter c && (c > 'Z') = V c
      | otherwise = error "Invalid expression - variables should be lowercase letters only"

    -- Identity is self dual
    parseNot :: Term -> Term
    parseNot O = O
    parseNot t = Not t

    -- Int value handles layers of nested seqs
    parseSeq :: Int -> [Term] -> [Char] -> String -> Term
    parseSeq 0 ts ys (x : xs)
      | x == '<' = parseSeq 1 ts (x : ys) xs
      | x == '>' && null xs = Seq (reverse (parse (reverse ys) : ts))
      | x == '>' = error "Invalid expression - invalid sequence of characters"
      | x == ';' = parseSeq 0 (parse (reverse ys) : ts) [] xs
      | otherwise = parseSeq 0 ts (x : ys) xs
    parseSeq n ts ys (x : xs)
      | x == '>' = parseSeq (n - 1) ts (x : ys) xs
      | x == '<' = parseSeq (n + 1) ts (x : ys) xs
      | otherwise = parseSeq n ts (x : ys) xs

    -- Int value handles layers of nested par/copar
    parsePar :: Int -> [Term] -> [Char] -> String -> Term
    parsePar 0 ts ys (x : xs)
      | x == '(' = parsePar 1 ts (x : ys) xs
      | x == '[' = parsePar 1 ts (x : ys) xs
      | x == ']' && null xs = Par (reverse (parse (reverse ys) : ts))
      | x == ']' = error "Invalid expression - invalid sequence of characters"
      | x == ',' = parsePar 0 (parse (reverse ys) : ts) [] xs
      | otherwise = parsePar 0 ts (x : ys) xs
    parsePar n ts ys (x : xs)
      | x == ')' = parsePar (n - 1) ts (x : ys) xs
      | x == ']' = parsePar (n - 1) ts (x : ys) xs
      | x == '(' = parsePar (n + 1) ts (x : ys) xs
      | x == '[' = parsePar (n + 1) ts (x : ys) xs
      | otherwise = parsePar n ts (x : ys) xs

    -- Int value handles layers of nested par/copar
    parseCopar :: Int -> [Term] -> [Char] -> String -> Term
    parseCopar 0 ts ys (x : xs)
      | x == '(' = parseCopar 1 ts (x : ys) xs
      | x == '[' = parseCopar 1 ts (x : ys) xs
      | x == ')' && null xs = Copar (reverse (parse (reverse ys) : ts))
      | x == ')' = error "Invalid expression - invalid sequence of characters"
      | x == ',' = parseCopar 0 (parse (reverse ys) : ts) [] xs
      | otherwise = parseCopar 0 ts (x : ys) xs
    parseCopar n ts ys (x : xs)
      | x == ')' = parseCopar (n - 1) ts (x : ys) xs
      | x == ']' = parseCopar (n - 1) ts (x : ys) xs
      | x == '(' = parseCopar (n + 1) ts (x : ys) xs
      | x == '[' = parseCopar (n + 1) ts (x : ys) xs
      | otherwise = parseCopar n ts (x : ys) xs

-- Outputs a Term as a string, acting as a logical inverse to the parse function
outputTerm :: Term -> String
outputTerm x = case x of
  O -> "O"
  V x -> x : ""
  Not x -> "-" ++ outputTerm x
  Seq xs -> "<" ++ intercalate ";" [outputTerm x | x <- xs] ++ ">"
  Par xs -> "[" ++ intercalate "," [outputTerm x | x <- xs] ++ "]"
  Copar xs -> "(" ++ intercalate "," [outputTerm x | x <- xs] ++ ")"

-- Outputs a list of Terms in a more readable way
outputTerms :: [Term] -> ShowS
outputTerms [] "" = "None"
outputTerms ts "" = intercalate "\n" [outputTerm t | t <- ts]

-- Outputs a proof in a more readable way
outputProof :: Proof -> IO ()
outputProof proof = putStrLn ("\n" ++ (intercalate "\n" [ruleUsed t p ++ outputTerm t | (t, p) <- shift proof ' ']) ++ "\n")
  where
    ruleUsed :: Term -> Char -> String
    ruleUsed t p = replicate (length (outputTerm t)) '-' ++ [p] ++ "\n"

    -- Moves all rules down a level and adds the o rule instead to the O Term
    -- Improves readability
    shift :: Proof -> Char -> Proof
    shift [] _ = []
    shift ((t, p) : ps) ' ' = (O, 'o') : shift ps p
    shift ((t, p) : ps) p' = (t, p') : shift ps p

outputMaybeProof :: Maybe Proof -> IO ()
outputMaybeProof (Just p) = outputProof p
outputMaybeProof Nothing = putStrLn "No proof found"

---------------------------------------------------------------------------------
---------------------------Equivalence-------------------------------------------
---------------------------------------------------------------------------------

-- Infix functions to check 2 preprocessed Terms are equivalent/ not equivalent
-- modulo commutativity of par and copar
(~=) :: Term -> Term -> Bool
O ~= O = True
Seq [] ~= O = True
Par [] ~= O = True
Copar [] ~= O = True
V x ~= V y = x == y
Not t1 ~= Not t2 = t1 ~= t2
Seq t1 ~= Seq t2 = length t1 == length t2 && all equivTuple (zip t1 t2)
  where
    equivTuple :: (Term, Term) -> Bool
    equivTuple (t1, t2) = t1 ~= t2
Par t1 ~= Par t2 = null (t1 \\ t2) && null (t2 \\ t1) -- equal up to order
Copar t1 ~= Copar t2 = null (t1 \\ t2) && null (t2 \\ t1) -- equal up to order
_ ~= _ = False

(/~=) :: Term -> Term -> Bool
t1 /~= t2 = not (t1 ~= t2)

removeId :: Term -> Term
removeId x = case x of
  Seq ts -> Seq (filter (/= O) (map removeId ts))
  Par ts -> Par (filter (/= O) (map removeId ts))
  Copar ts -> Copar (filter (/= O) (map removeId ts))
  Not t -> Not (removeId t)
  t -> t

-- Puts a Term into negation normal form
negationNormal :: Term -> Term
negationNormal t = doubleNegative (deMorgan (doubleNegative t))
  where
    -- Recursively applies De Morgan's laws to push negation to atoms
    deMorgan :: Term -> Term
    deMorgan x = case x of
      Not (Seq ts) -> deMorgan (Seq [Not (deMorgan t) | t <- ts])
      Not (Par ts) -> deMorgan (Copar [Not (deMorgan t) | t <- ts])
      Not (Copar ts) -> deMorgan (Par [Not (deMorgan t) | t <- ts])
      Seq ts -> Seq [deMorgan t | t <- ts]
      Par ts -> Par [deMorgan t | t <- ts]
      Copar ts -> Copar [deMorgan t | t <- ts]
      t -> t

    -- Removes double negatives
    doubleNegative :: Term -> Term
    doubleNegative x = case x of
      Not (Not t) -> doubleNegative t
      Seq ts -> Seq [doubleNegative t | t <- ts]
      Par ts -> Par [doubleNegative t | t <- ts]
      Copar ts -> Copar [doubleNegative t | t <- ts]
      t -> t

-- Flattens instances of a structure nested within the same structure
associate :: Term -> Term
associate x = case x of
  Seq ts -> Seq (concat [unSeq t | t <- ts])
  Par ts -> Par (concat [unPar t | t <- ts])
  Copar ts -> Copar (concat [unCopar t | t <- ts])
  t -> t
  where
    unSeq :: Term -> [Term]
    unSeq (Seq ts) = concat [unSeq t | t <- ts]
    unSeq t = [associate t]

    unPar :: Term -> [Term]
    unPar (Par ts) = concat [unPar t | t <- ts]
    unPar t = [associate t]

    unCopar :: Term -> [Term]
    unCopar (Copar ts) = concat [unCopar t | t <- ts]
    unCopar t = [associate t]

-- Any singleton structures are replaced by just the element itself
extractSingleton :: Term -> Term
extractSingleton (Seq (t : ts))
  | null ts = extractSingleton t
  | otherwise = Seq [extractSingleton a | a <- t : ts]
extractSingleton (Par (t : ts))
  | null ts = extractSingleton t
  | otherwise = Par [extractSingleton a | a <- t : ts]
extractSingleton (Copar (t : ts))
  | null ts = extractSingleton t
  | otherwise = Copar [extractSingleton a | a <- t : ts]
extractSingleton t = t

-- Applies all of the above functions in order to put any Term in its normal form
-- Defined such that any 2 logically equivalent Terms t1 and t2 will satisfy t1 ~= t2 once normalised
preprocess :: Term -> Term
preprocess t = associate (extractSingleton (negationNormal (removeId t)))

---------------------------------------------------------------------------------
-----------------------------Rewrite Rules---------------------------------------
---------------------------------------------------------------------------------

-- Deep inference logic that applies a given function to one element at a time of the given list
-- and leaves the others unchanged
deepInference :: [Term] -> (Term -> [Term]) -> [[Term]]
deepInference ts f = di [] ts f \\ [ts]
  where
    di :: [Term] -> [Term] -> (Term -> [Term]) -> [[Term]]
    di seen [] f = []
    di seen (t : ts) f = [reverse seen ++ [s] ++ ts | s <- f t] ++ di (t : seen) ts f

-- Returns all lists that can be constructed with any number of elements of the given list
powerset :: Eq a => [a] -> [[a]]
powerset x = nub (pows x)
  where
    pows :: [a] -> [[a]]
    pows [] = [[]]
    pows (x : xs) = [x : ps | ps <- pows xs] ++ pows xs

-- Gets a list of every letter that has been used as a variable in a Term
getUsedAtoms :: Term -> [Char]
getUsedAtoms x = case x of
  O -> []
  V t -> [t]
  Not (V t) -> [t]
  Seq ts -> nub (concat [getUsedAtoms t | t <- ts])
  Par ts -> nub (concat [getUsedAtoms t | t <- ts])
  Copar ts -> nub (concat [getUsedAtoms t | t <- ts])

-- Removes a [a, Not a] pair from a Par structure for a specified variable a
oneiDown :: Char -> Term -> [Term]
oneiDown a (Par ts)
  | not (isLetter a && a > 'Z') = error "Invalid rewrite - Variables must be lowercase letters only"
  | otherwise = down [] False False a ts
  where
    down :: [Term] -> Bool -> Bool -> Char -> [Term] -> [Term]
    down seen False False a (t : ts)
      | t == V a = down seen True False a ts
      | t == Not (V a) = down seen False True a ts
      | otherwise = down (t : seen) False False a ts
    down seen True False a (t : ts)
      | t == V a = down (V a : seen) True False a ts
      | t == Not (V a) = [Par (reverse seen ++ ts)]
      | otherwise = down (t : seen) True False a ts
    down seen False True a (t : ts)
      | t == V a = [Par (reverse seen ++ ts)]
      | t == Not (V a) = down (Not (V a) : seen) False True a ts
      | otherwise = down (t : seen) False True a ts
    down _ _ _ _ [] = []
oneiDown _ _ = []

-- Adds a Copar pair (a, Not a) to any Par or Copar Term; if Term is a Seq, will put this pair in
-- every possible position
oneiUp :: Char -> Term -> [Term]
oneiUp c t
  | not (isLetter c && c > 'Z') = error "Invalid rewrite - Variables must be lowercase letters only"
  | otherwise = up c t
  where
    up :: Char -> Term -> [Term]
    up c x = case x of
      Seq ts ->
        [ Seq (take n ts ++ [Copar [V c, Not (V c)]] ++ drop n ts)
          | n <- [0 .. length ts]
        ]
      Par ts -> [Par (ts ++ [Copar [V c, Not (V c)]])]
      Copar ts -> [Copar (ts ++ [V c, Not (V c)])]
      t -> [Copar [t, V c, Not (V c)]] -- currently not allowing this case in aiUp

-- Generates a list of all possible aiDown rewrites of a Term
aiDown :: Term -> [Term]
aiDown x = case x of
  Par ts ->
    nub
      ( map
          preprocess
          ( concat [oneiDown a (Par ts) | a <- getUsedAtoms (Par ts)]
              ++ [Par t | t <- deepInference ts aiDown]
          )
      )
  Copar ts -> nub [preprocess (Copar t) | t <- deepInference ts aiDown]
  Seq ts -> nub [preprocess (Seq t) | t <- deepInference ts aiDown]
  t -> []

-- Generates a list of all possible aiUp rewrites of a Term
aiUp :: Term -> [Term]
aiUp x = case x of
  Seq ts ->
    concat [oneiUp a (Seq ts) | a <- getUsedAtoms (Seq ts)]
      ++ [Seq t | t <- deepInference ts aiUp]
  Par ts ->
    concat [oneiUp a (Par ts) | a <- getUsedAtoms (Par ts)]
      ++ [Par t | t <- deepInference ts aiUp]
  Copar ts ->
    concat [oneiUp a (Copar ts) | a <- getUsedAtoms (Copar ts)]
      ++ [Copar t | t <- deepInference ts aiUp]
  t -> []

-- Generates a list of all possible single step switches of a Term
switch :: Term -> [Term]
switch x = case x of
  Par ts ->
    swtch ts ++ [preprocess (Par t) | t <- deepInference ts switch]
  Copar ts -> nub [preprocess (Copar t) | t <- deepInference ts switch]
  Seq ts -> nub [preprocess (Seq t) | t <- deepInference ts switch]
  t -> []
  where
    swtch :: [Term] -> [Term]
    swtch ts =
      nub
        ( map
            preprocess
            ( concat [permute ts' | ts' <- extractCopar ts]
                ++ degenerate ts
            )
        )
        \\ [Par ts]
    -- Returns a list of tuples where each is of the form
    -- ([Terms inside a copar element of the given list],[All other Terms])
    extractCopar :: [Term] -> [([Term], [Term])]
    extractCopar = ec []
      where
        ec :: [Term] -> [Term] -> [([Term], [Term])]
        ec seen (Copar ts : unseen) = (ts, reverse seen ++ unseen) : ec (Copar ts : seen) unseen
        ec seen (x : unseen) = ([x], reverse seen ++ unseen) : ec (x : seen) unseen
        ec seen [] = []

    permute :: ([Term], [Term]) -> [Term]
    permute (as, bs) =
      [ Par (Copar (Par (Copar a : b) : (as \\ a)) : (bs \\ b))
        | a <- powerset as,
          b <- powerset bs
      ]

    degenerate :: [Term] -> [Term]
    degenerate ts = [Par (Copar ts' : (ts \\ ts')) | ts' <- powerset ts]

-- Generates a list of all possible single step qDown applications of a Term
qDown :: Term -> [Term]
qDown x = case x of
  Par ts ->
    qd ts ++ nub [preprocess (Par t) | t <- deepInference ts qDown]
  Copar ts -> nub [preprocess (Copar t) | t <- deepInference ts qDown]
  Seq ts -> nub [preprocess (Seq t) | t <- deepInference ts qDown]
  t -> []
  where
    qd :: [Term] -> [Term]
    qd ts =
      nub
        ( map
            preprocess
            ( noSeq ts
                ++ oneSeq ts
                ++ twoSeq ts
            )
        )
        \\ [Par ts]

    -- Split any Par Term into 3 (possibly empty) parts, impose an ordering on two of them,
    -- and put that ordering inside of a Par context with the third
    noSeq :: [Term] -> [Term]
    noSeq ts =
      concat
        ( concat
            [ [ [ Par (Seq [Par (as \\ bs), Par bs] : (ts \\ as)),
                  Par (Seq [Par bs, Par (as \\ bs)] : (ts \\ as))
                ]
                | bs <- powerset as
              ]
              | as <- powerset ts
            ]
        )

    -- For each proper seq substructure of an arbitrary par structure, splits said seq substructure
    -- into 2 (possibly empty) ordered parts ⟨A⟩, ⟨B⟩, splits the remaining elements of the par into
    -- 2 (possibly empty) parts [C], [D], and return two rewrites [⟨[⟨A⟩C];B⟩,D] and [⟨A;[⟨B⟩,C]⟩,D]
    oneSeq :: [Term] -> [Term]
    oneSeq ts = concat [oseq t (ts \\ [Seq t]) | t <- getSeqs ts]
      where
        oseq :: [Term] -> [Term] -> [Term]
        oseq seqs ts =
          concat
            [ [ Par (Seq (Par (Seq s : t) : (seqs \\ s)) : (ts \\ t)),
                Par (Seq (s ++ [Par (Seq (seqs \\ s) : t)]) : (ts \\ t))
              ]
              | s <- orderedSplit seqs,
                t <- powerset ts
            ]

    -- For each pair of proper seq sub
    twoSeq :: [Term] -> [Term]
    twoSeq ts = concat [tseq a b (ts \\ [Seq a, Seq b]) | (a, b) <- takeTwo (getSeqs ts)]
      where
        tseq :: [Term] -> [Term] -> [Term] -> [Term]
        tseq a b ts =
          [ Par (Seq [Par [Seq as, Seq bs], Par [Seq (a \\ as), Seq (b \\ bs)]] : ts)
            | as <- orderedSplit a,
              bs <- orderedSplit b
          ]

        takeTwo :: [a] -> [(a, a)]
        takeTwo [] = []
        takeTwo (t : ts) = [(t, t') | t' <- ts] ++ takeTwo ts

    getSeqs :: [Term] -> [[Term]]
    getSeqs [] = []
    getSeqs ((Seq t) : ts) = t : getSeqs ts
    getSeqs (t : ts) = getSeqs ts

    orderedSplit :: [a] -> [[a]]
    orderedSplit = os []
      where
        os :: [a] -> [a] -> [[a]]
        os seen [] = [reverse seen]
        os seen (s : seqs) = reverse seen : os (s : seen) seqs

-- Generates a list of all possible single step qUp applications of a Term
qUp :: Term -> [Term]
qUp x = case x of
  Seq ts ->
    nub
      ( map
          preprocess
          ( [Copar t | t <- uncurry permute (extractCopar ts)]
              ++ [Seq t | t <- deepInference ts qUp]
          )
      )
      \\ [Seq ts]
  Copar ts -> nub [preprocess (Copar t) | t <- deepInference ts qUp]
  Par ts -> nub [preprocess (Par t) | t <- deepInference ts qUp]
  t -> []
  where
    -- Given a list of Terms, returns ([],[]) unless the list is precicely 2 Copar structures
    -- and nothing more, in which case it returns ([Terms in first Copar], [Terms in second Copar])
    extractCopar :: [Term] -> ([Term], [Term])
    extractCopar = ec [] []
      where
        ec :: [Term] -> [Term] -> [Term] -> ([Term], [Term])
        ec [] [] (Copar ts : rest) = ec ts [] rest
        ec first [] (Copar ts : rest) = ec first ts rest
        ec first second [] = (first, second)
        ec _ _ t = ([], [])

    permute :: [Term] -> [Term] -> [[Term]]
    permute [] [] = []
    permute as bs =
      [ [Seq [Copar a, Copar b], Seq [Copar (as \\ a), Copar (bs \\ b)]]
        | a <- powerset as,
          b <- powerset bs
      ]

    powerset :: [a] -> [[a]]
    powerset [] = [[]]
    powerset (x : xs) = [x : ps | ps <- powerset xs] ++ powerset xs

---------------------------------------------------------------------------------
-----------------------------Proof Search Algorithm------------------------------
---------------------------------------------------------------------------------

-- Finds all single step rewrites of a possible Term, and records which rule was used to get there
reachable :: Term -> [(Term, Char)]
reachable t =
  nub
    ( -- commented out up for development purposes
      [(ts, 'a') | ts <- aiDown t]
        -- ++ [(ts, 'A') | ts <- aiUp t]
        ++ [(ts, 's') | ts <- switch t]
        -- ++ [(ts, 'Q') | ts <- qUp t]
        ++ [(ts, 'q') | ts <- qDown t]
    )

-- CURRENTLY UNUSED
lenTerm :: Term -> Int
lenTerm x = case x of
  Seq ts -> sum [lenTerm t | t <- ts]
  Par ts -> sum [lenTerm t | t <- ts]
  Copar ts -> sum [lenTerm t | t <- ts]
  Not t -> 1
  V v -> 1
  O -> 0

proofSearch :: Term -> [Proof]
proofSearch t = doBfsearch [] [(t, '_')]
  where
    doBfsearch :: [Term] -> Proof -> [Proof]
    doBfsearch seen proof
      | fst (proof !! 0) `elem` seen = []
      | fst (proof !! 0) == O = [proof]
      | otherwise =
          concat
            [ doBfsearch (fst (proof !! 0) : seen) proof'
              | proof' <- [(t, p) : proof | (t, p) <- reachable (fst (proof !! 0))]
            ]

slightlyBetterBfs :: Term -> Maybe Proof
slightlyBetterBfs start = loop [[(start, '_')]] [] -- minimumBy (compare `on` length)
  where
    loop :: [Proof] -> [Term] -> Maybe Proof
    loop frontier seen
      | any isDone frontier = find isDone frontier
      | otherwise =
          loop
            (filter (\p -> notElem (fst (p !! 0)) seen) rs)
            (seen ++ [fst (r !! 0) | r <- rs])
      where
        rs = nub $ concat [[r : p | r <- reachable (fst (p !! 0))] | p <- frontier]

    isDone :: Proof -> Bool
    isDone p = fst (p !! 0) == O

prove :: IO ()
prove = runInputT defaultSettings prv
  where
    prv :: InputT IO ()
    prv = do
      input <- getInputLine "Enter SBV structure to prove:\n"
      outputStrLn "Searching for proof..."
      case input of
        Just x -> liftIO (mapM_ outputProof (proofSearch (preprocess (parse x))))
        Nothing -> outputStrLn "Invalid input - ????"
      outputStrLn "Proof search finished"

motivate :: IO ()
motivate = putStrLn "you got this <3"

rab :: String -> [Term]
rab t = map fst (reachable (preprocess (parse t)))

{-
Testing material

1: [(a,b),-a,-b]
2: [<a;(b,-a)>,[b,a,-a]]
3: [<a;(b,c);d>,<[-a,-b];-d>,c]
4: [c,<-c;[b,(-b,[a,-a])]>]

Proofs of (1):

-o
O
------a
[b,-b]
---------------a
[([a,-a],b),-b]
-------------s
[(a,b),-a,-b]

-o
O
------a
[a,-a]
---------------a
([b,-b],[a,-a])
---------------s
[([a,-a],b),-b]
-------------s
[(a,b),-a,-b]

-o
O
------a
[b,-b]
---------------a
([b,-b],[a,-a])
---------------s
[([a,-a],b),-b]
-------------s
[(a,b),-a,-b]

-o
O
------a
[a,-a]
---------------a
[([b,-b],a),-a]
-------------s
[(a,b),-a,-b]

-o
O
------a
[b,-b]
---------------a
([a,-a],[b,-b])
---------------s
[([b,-b],a),-a]
-------------s
[(a,b),-a,-b]

-o
O
------a
[a,-a]
---------------a
([a,-a],[b,-b])
---------------s
[([b,-b],a),-a]
-------------s
[(a,b),-a,-b]
-}
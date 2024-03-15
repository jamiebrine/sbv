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
import Distribution.Simple (ProfDetailLevel (ProfDetailToplevelFunctions))
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
  str -> error "Invalid expression - invalid sequence of characters"
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
      | x == '>' = Seq (reverse (parse (reverse ys) : ts))
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
      | x == ']' = Par (reverse (parse (reverse ys) : ts))
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
      | x == ')' = Copar (reverse (parse (reverse ys) : ts))
      | x == ',' = parseCopar 0 (parse (reverse ys) : ts) [] xs
      | otherwise = parseCopar 0 ts (x : ys) xs
    parseCopar n ts ys (x : xs)
      | x == ')' = parseCopar (n - 1) ts (x : ys) xs
      | x == ']' = parseCopar (n - 1) ts (x : ys) xs
      | x == '(' = parseCopar (n + 1) ts (x : ys) xs
      | x == '[' = parseCopar (n + 1) ts (x : ys) xs
      | otherwise = parseCopar n ts (x : ys) xs

-- Outputs a term as a string, acting as a logical inverse to the parse function
outputTerm :: Term -> String
outputTerm x = case x of
  O -> "O"
  V x -> x : ""
  Not x -> "-" ++ outputTerm x
  Seq xs -> "<" ++ intercalate ";" [outputTerm x | x <- xs] ++ ">"
  Par xs -> "[" ++ intercalate "," [outputTerm x | x <- xs] ++ "]"
  Copar xs -> "(" ++ intercalate "," [outputTerm x | x <- xs] ++ ")"

-- Outputs a list of terms in a more readable way
outputTerms :: [Term] -> ShowS
outputTerms [] "" = "None"
outputTerms ts "" = intercalate "\n" [outputTerm t | t <- ts]

-- Outputs a proof in a more readable way
outputProof :: Proof -> IO ()
outputProof proof = putStrLn ("\n" ++ (intercalate "\n" [ruleUsed t p ++ outputTerm t | (t, p) <- shift proof ' ']) ++ "\n")
  where
    ruleUsed :: Term -> Char -> String
    ruleUsed t p = replicate (length (outputTerm t)) '-' ++ [p] ++ "\n"

    -- Moves all rules down a level and adds the o rule instead to the O term
    -- Improves readability
    shift :: Proof -> Char -> Proof
    shift [] _ = []
    shift ((t, p) : ps) ' ' = (t, 'o') : shift ps p
    shift ((t, p) : ps) p' = (t, p') : shift ps p

outputMaybeProof :: Maybe Proof -> IO ()
outputMaybeProof (Just p) = outputProof p
outputMaybeProof Nothing = putStrLn "No proof found"

---------------------------------------------------------------------------------
---------------------------Normalise Terms---------------------------------------
---------------------------------------------------------------------------------

-- Infix functions to check 2 terms are equivalent/ not equivalent
-- modulo commutativity of par and copar
(~=) :: Term -> Term -> Bool
O ~= O = True
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

-- Removes any lone O terms and empty sequences from inside a Seq, Par, or Copar
removeId :: Term -> Term
removeId x
  | x == y = x
  | otherwise = removeId y
  where
    y = rmvId x

    -- Iteratively applies this function until the result is unchanged
    rmvId :: Term -> Term
    rmvId x = case x of
      Seq [] -> O
      Par [] -> O
      Copar [] -> O
      Seq ts -> Seq (rmv [] ts)
      Par ts -> Par (rmv [] ts)
      Copar ts -> Copar (rmv [] ts)
      Not ts -> Not (rmvId ts)
      t -> t
      where
        rmv :: [Term] -> [Term] -> [Term]
        rmv kept (O : ts) = rmv kept ts
        rmv kept (Seq [] : ts) = rmv kept ts
        rmv kept (Par [] : ts) = rmv kept ts
        rmv kept (Copar [] : ts) = rmv kept ts
        rmv kept (t : ts) = rmv (rmvId t : kept) ts
        rmv kept [] = reverse kept

-- Recursively applies de morgan's laws to put a term into negation normal form
deMorgan :: Term -> Term
deMorgan x = case x of
  Not (Seq ts) -> deMorgan (Seq [Not (deMorgan t) | t <- ts])
  Not (Par ts) -> deMorgan (Copar [Not (deMorgan t) | t <- ts])
  Not (Copar ts) -> deMorgan (Par [Not (deMorgan t) | t <- ts])
  Seq ts -> Seq [deMorgan t | t <- ts]
  Par ts -> Par [deMorgan t | t <- ts]
  Copar ts -> Copar [deMorgan t | t <- ts]
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

-- Removes double negatives
doubleNegative :: Term -> Term
doubleNegative x = case x of
  Not (Not t) -> doubleNegative t
  Seq ts -> Seq [doubleNegative t | t <- ts]
  Par ts -> Par [doubleNegative t | t <- ts]
  Copar ts -> Copar [doubleNegative t | t <- ts]
  t -> t

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

-- Applies all of the above functions in order to put any term in its normal form
-- Defined such that any 2 logically equivalent terms t1 and t2 will satisfy t1 ~= t2 once normalised
normalise :: Term -> Term
normalise t = associate (extractSingleton (doubleNegative (deMorgan (removeId t))))

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
powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x : xs) = [x : ps | ps <- powerset xs] ++ powerset xs

-- Gets a list of every letter that has been used as a variable in a term
getUsedAtoms :: Term -> [Char]
getUsedAtoms x = case x of
  Seq ts -> nub (concat [getUsedAtoms t | t <- ts])
  Par ts -> nub (concat [getUsedAtoms t | t <- ts])
  Copar ts -> nub (concat [getUsedAtoms t | t <- ts])
  Not (V t) -> [t]
  V t -> [t]
  O -> []

-- Removes a [a, Not a] pair from a Par structure for a specified variable a
oneiDown :: Char -> Term -> Term
oneiDown a (Par ts) = Par (down [] False False a ts)
  where
    down :: [Term] -> Bool -> Bool -> Char -> [Term] -> [Term]
    down seen False False a (t : ts)
      | t == V a = down seen True False a ts
      | t == Not (V a) = down seen False True a ts
      | otherwise = down (t : seen) False False a ts
    down seen True False a (t : ts)
      | t == V a = down (V a : seen) True False a ts
      | t == Not (V a) = reverse seen ++ ts
      | otherwise = down (t : seen) True False a ts
    down seen False True a (t : ts)
      | t == V a = reverse seen ++ ts
      | t == Not (V a) = down (Not (V a) : seen) False True a ts
      | otherwise = down (t : seen) False True a ts
    down seen pos neg a []
      | pos = V a : reverse seen
      | neg = Not (V a) : reverse seen
      | otherwise = reverse seen
oneiDown a t = t

-- Adds a Copar pair (a, Not a) to any Par or Copar term; if term is a Seq, will put this pair in
-- every possible position and return a single Par whose elements are these possible rewrites,
-- which will then be unpacked by the alliUp function that calls it
oneiUp :: Char -> Term -> Term
oneiUp c t
  | not (isLetter c && c > 'Z') = error "Invalid rewrite - Variables must be lowercase letters only"
  | otherwise = normalise (up c t)
  where
    up :: Char -> Term -> Term
    up c (Seq ts) = upSeq c ts
    up c (Par ts) = Par (ts ++ [Copar [V c, Not (V c)]])
    up c (Copar ts) = Copar (ts ++ [Copar [V c, Not (V c)]])
    up c t = Copar [t, V c, Not (V c)]

    upSeq :: Char -> [Term] -> Term
    upSeq c ts = Par [Seq (take n ts ++ [Copar [V c, Not (V c)]] ++ drop n ts) | n <- [0 .. length ts]]

-- Generates a list of all possible aiDown rewrites of a term
aiDown :: Term -> [Term]
aiDown x = case x of
  Par ts ->
    nub
      ( map
          normalise
          ( [oneiDown a (Par ts) | a <- getUsedAtoms (Par ts)]
              ++ [Par t | t <- deepInference ts aiDown]
          )
      )
      \\ [Par ts]
  Copar ts -> nub [normalise (Copar t) | t <- deepInference ts aiDown]
  Seq ts -> nub [normalise (Seq t) | t <- deepInference ts aiDown]
  t -> []

-- Generates a list of all possible aiUp rewrites of a term
aiUp :: Term -> [Term]
aiUp x = case x of
  Seq ts ->
    nub
      --   ( map
      --     normalise
      ( concat [ts | Par ts <- [oneiUp a (Seq ts) | a <- getUsedAtoms (Seq ts)]]
          ++ [Seq t | t <- deepInference ts aiUp]
      )
      --    )
      \\ [Seq ts]
  Par ts ->
    nub
      --   ( map
      --      normalise
      ( [oneiUp a (Par ts) | a <- getUsedAtoms (Par ts)]
          ++ [Par t | t <- deepInference ts aiUp]
      )
      --      )
      \\ [Par ts]
  Copar ts ->
    nub
      --  ( map
      --      normalise
      ( [oneiUp a (Copar ts) | a <- getUsedAtoms (Copar ts)]
          ++ [Copar t | t <- deepInference ts aiUp]
      )
      --    )
      \\ [Copar ts]
  t -> []

-- Generates a list of all possible single step switches of a term
switch :: Term -> [Term]
switch x = case x of
  Par ts ->
    nub
      ( map
          normalise
          ( [Par t | t <- concat [uncurry permute ts' | ts' <- extractCopar ts]]
              ++ [Par t | t <- deepInference ts switch]
          )
      )
      \\ [Par ts]
  Copar ts -> nub [normalise (Copar t) | t <- deepInference ts switch]
  Seq ts -> nub [normalise (Seq t) | t <- deepInference ts switch]
  t -> []
  where
    -- Returns a list of tuples where each is of the form
    -- ([Terms inside a copar element of the given list],[All other terms])
    extractCopar :: [Term] -> [([Term], [Term])]
    extractCopar = ec []
      where
        ec :: [Term] -> [Term] -> [([Term], [Term])]
        ec seen (Copar ts : unseen) = (ts, reverse seen ++ unseen) : ec (Copar ts : seen) unseen
        ec seen (x : unseen) = ([x], reverse seen ++ unseen) : ec (x : seen) unseen
        ec seen [] = [([], reverse seen), (reverse seen, [])]

    permute :: [Term] -> [Term] -> [[Term]]
    permute as bs =
      [ Copar (Par (Copar a : b) : (as \\ a)) : (bs \\ b)
        | a <- powerset as,
          b <- powerset bs
      ]

-- Generates a list of all possible single step qDown applications of a term
qDown :: Term -> [Term]
qDown x = case x of
  Par ts ->
    nub
      ( map
          normalise
          ( concat [[Par (t' : (ts \\ ts')) | t' <- permute (extractSeqs ts')] | ts' <- powerset ts]
              ++ [Par t | t <- deepInference ts qDown]
          )
      )
      \\ [Par ts]
  Copar ts -> nub [normalise (Copar t) | t <- deepInference ts qDown]
  Seq ts -> nub [normalise (Seq t) | t <- deepInference ts qDown]
  t -> []
  where
    -- Returns a list of all sublists that begin with the first element
    getSublists :: [a] -> [[a]]
    getSublists [] = []
    getSublists (x : xs) = [x] : [x : ys | ys <- getSublists xs]

    extractSeqs :: [Term] -> [([Term], [Term])]
    extractSeqs ts = es [] [] ts ++ [([Par t], [Par (ts \\ t)]) | t <- powerset ts]
      where
        -- Seperates list of terms into
        es :: [[Term]] -> [Term] -> [Term] -> [([Term], [Term])]
        es seqs [] [Seq ts, Seq ts'] = [(ts, ts')]
        es seqs seen (Seq ts : unseen) = es (ts : seqs) seen unseen
        es seqs seen (x : unseen) = es seqs (x : seen) unseen
        es seqs seen [] =
          [ (s, [Par ([Seq s' | s' <- seqs \\ [s]] ++ seen)])
            | s <- seqs
          ]

    permute :: [([Term], [Term])] -> [Term]
    permute ts =
      concat
        [ [ Seq [Par [Seq a, Seq b], Par [Seq (as \\ a), Seq (bs \\ b)]]
            | a <- getSublists as,
              b <- getSublists bs
          ]
          | (as, bs) <- ts
        ]

-- CURRENTLY USING THIS
qDown' :: Term -> [Term]
qDown' x = case x of
  Par ts ->
    nub
      ( concat [[normalise (Par (t' : (ts \\ subset))) | t' <- makeSeq subset] | subset <- powerset ts]
          ++ [normalise (Par t) | t <- deepInference ts qDown']
      )
      \\ [Par ts]
  Copar ts -> nub [normalise (Copar t) | t <- deepInference ts qDown']
  Seq ts -> nub [normalise (Seq t) | t <- deepInference ts qDown']
  t -> []
  where
    getSublists :: [a] -> [[a]]
    getSublists [] = []
    getSublists (x : xs) = [x] : [x : ys | ys <- getSublists xs]

    makeSeq :: [Term] -> [Term]
    makeSeq ts = map normalise (permute (extractSeqs ts))
      where
        extractSeqs :: [Term] -> [([Term], [Term])]
        extractSeqs = es []
          where
            es :: [[Term]] -> [Term] -> [([Term], [Term])]
            es [] [Seq ts, Seq ts'] = [(ts, ts')]
            es seqs (Seq ts : unseen) = es (ts : seqs) unseen
            es seqs (x : unseen) = es ([O, x, O] : seqs) unseen
            es seqs [] = [(s, [Par [Seq s' | s' <- seqs \\ [s]]]) | s <- seqs]

        permute :: [([Term], [Term])] -> [Term]
        permute ts =
          concat
            [ [ normalise (Seq [Par [Seq a, Seq b], Par [Seq (as \\ a), Seq (bs \\ b)]])
                | a <- getSublists as,
                  b <- getSublists bs
              ]
              | (as, bs) <- ts
            ]

-- Generates a list of all possible single step qUp applications of a term
qUp :: Term -> [Term]
qUp x = case x of
  Seq ts ->
    nub
      ( map
          normalise
          ( [Copar t | t <- uncurry permute (extractCopar ts)]
              ++ [Seq t | t <- deepInference ts qUp]
          )
      )
      \\ [Seq ts]
  Copar ts -> nub [normalise (Copar t) | t <- deepInference ts qUp]
  Par ts -> nub [normalise (Par t) | t <- deepInference ts qUp]
  t -> []
  where
    -- Given a list of terms, returns ([],[]) unless the list is precicely 2 Copar structures
    -- and nothing more, in which case it returns ([terms in first Copar], [terms in second Copar])
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

-- Finds all single step rewrites of a possible term, and records which rule was used to get there
reachable :: (Term, Char) -> [(Term, Char)]
reachable (t, p) =
  nub
    ( -- commented out up for development purposes
      [(ts, 'a') | ts <- aiDown t]
        -- ++ [(ts, 'A') | ts <- aiUp t]
        ++ [(ts, 's') | ts <- switch t]
        -- ++ [(ts, 'Q') | ts <- qUp t]
        ++ [(ts, 'q') | ts <- qDown' t]
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

-- CURRENTLY UNUSED
proofSearch :: Term -> [Proof]
proofSearch t = doBfsearch [] [(t, '_')] -- minimumBy (compare `on` length)
  where
    doBfsearch :: [Term] -> Proof -> [Proof]
    doBfsearch seen proof
      | fst (proof !! 0) `elem` seen = []
      | fst (proof !! 0) == O = [proof]
      | otherwise =
          concat
            [ doBfsearch (fst (proof !! 0) : seen) proof'
              | proof' <- [(t, p) : proof | (t, p) <- reachable (proof !! 0)]
            ]

slightlyBetterBfs :: Term -> Maybe Proof
slightlyBetterBfs start = loop [[(start, '_')]] []
  where
    loop :: [Proof] -> [Term] -> Maybe Proof
    loop frontier seen
      | any isDone frontier = find isDone frontier
      | otherwise =
          loop
            (filter (\p -> notElem (fst (p !! 0)) seen) rs)
            (seen ++ [fst (r !! 0) | r <- rs])
      where
        rs = nub $ concat [[r : p | r <- reachable (p !! 0)] | p <- frontier]

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
        Just x -> liftIO (mapM_ outputProof (proofSearch (normalise (parse x))))
        Nothing -> outputStrLn "Invalid input - ????"
      outputStrLn "Proof search finished"

motivate :: IO ()
motivate = putStrLn "u got this <3"
module SBV (prove) where

---------------------------------------------------------------------------------
---------------------------Imports and Structures--------------------------------
---------------------------------------------------------------------------------

import Control.Monad.RWS (MonadIO (liftIO), gets)
import Data.Char (intToDigit, isLetter)
import Data.List (find, intercalate, minimumBy, nub, sort, subsequences, (\\))
import Debug.Trace (trace)
import System.Console.Haskeline
  ( InputT,
    defaultSettings,
    getInputLine,
    outputStrLn,
    runInputT,
  )

data Term = O | V Char | Not Term | Seq [Term] | Par [Term] | Copar [Term]

type Node = (Term, Char)

type Proof = [Node]

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
      | isLetter c && c > 'Z' = V c
      | otherwise = error "Invalid expression - variables should be lowercase letters only"

    -- Identity is self dual
    parseNot :: Term -> Term
    parseNot O = O
    parseNot t = Not t

    -- Int value handles layers of nested seqs
    parseSeq :: Int -> [Term] -> String -> String -> Term
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
    parsePar :: Int -> [Term] -> String -> String -> Term
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
    parseCopar :: Int -> [Term] -> String -> String -> Term
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
outputProof :: Maybe Proof -> String
outputProof x = case x of
  Nothing -> "No proof found (pVal = " ++ show pVal ++ ")"
  Just proof -> "\n" ++ (intercalate "\n" [ruleUsed t p ++ outputTerm t | (t, p) <- shift proof ' ']) ++ "\n"
  where
    ruleUsed :: Term -> Char -> String
    ruleUsed t p = replicate (length (outputTerm t)) '-' ++ [p] ++ "\n"

    -- Moves all rules down a level and adds the o rule instead to the O Term
    -- Improves readability
    shift :: Proof -> Char -> Proof
    shift [] _ = []
    shift ((t, p) : ps) ' ' = (O, 'o') : shift ps p
    shift ((t, p) : ps) p' = (t, p') : shift ps p

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

-- Removes empty sequences and identities from any Term
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

-- Returns each ordered two way split of a list
twoWaySplit :: [a] -> [([a], [a])]
twoWaySplit ts = [splitAt n ts | n <- [0 .. length ts]]

-- Returns each subset of a list with it's complement
twoWayPermute :: Eq a => [a] -> [([a], [a])]
twoWayPermute ts = [(t, ts \\ t) | t <- powerset ts]
  where
    -- Returns all lists that can be constructed with any number of elements of the given list
    powerset :: Eq a => [a] -> [[a]]
    powerset x = nub (pows x)
      where
        pows :: [a] -> [[a]]
        pows [] = [[]]
        pows (x : xs) = [x : ps | ps <- pows xs] ++ pows xs

-- Gets a list of every letter that has been used as a variable in a Term
getUsedAtoms :: Term -> String
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
aiUp t = nub $ iUp t (getUsedAtoms t)
  where
    iUp :: Term -> [Char] -> [Term]
    iUp x chars = case x of
      Seq ts ->
        concat [oneiUp a (Seq ts) | a <- chars]
          ++ [Seq t | t <- deepInference ts aiUp]
      Par ts ->
        concat [oneiUp a (Par ts) | a <- chars]
          ++ [Par t | t <- deepInference ts aiUp]
      Copar ts ->
        concat [oneiUp a (Copar ts) | a <- chars]
          ++ [Copar t | t <- deepInference ts aiUp]
      t -> concat [oneiUp a t | a <- chars]

-- Generates a list of all possible switch rewrites of a Term
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
      [ Par (Copar (Par (Copar a1 : b1) : a2) : b2)
        | (a1, a2) <- twoWayPermute as,
          (b1, b2) <- twoWayPermute bs
      ]

    degenerate :: [Term] -> [Term]
    degenerate ts = [Par (Copar t1 : t2) | (t1, t2) <- twoWayPermute ts]

-- Generates a list of all possible qDown rewrites of a Term
qDown :: Term -> [Term]
qDown x = case x of
  Par ts ->
    qdwn ts ++ nub [preprocess (Par t) | t <- deepInference ts qDown]
  Copar ts -> nub [preprocess (Copar t) | t <- deepInference ts qDown]
  Seq ts -> nub [preprocess (Seq t) | t <- deepInference ts qDown]
  t -> []
  where
    qdwn :: [Term] -> [Term]
    qdwn ts =
      nub $
        map
          preprocess
          ( noSeq ts
              ++ oneSeq ts
              ++ twoSeq ts
          )
          \\ [Par ts]

    -- Split any Par Term into 3 (possibly empty) parts, impose an ordering on two of them,
    -- and put that ordering inside of a Par context with the third
    noSeq :: [Term] -> [Term]
    noSeq ts =
      concat
        ( concat
            [ [ [ Par (Seq [Par b2, Par b1] : a2),
                  Par (Seq [Par b1, Par b2] : a2)
                ]
                | (b1, b2) <- twoWayPermute a1
              ]
              | (a1, a2) <- twoWayPermute ts
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
            [ [ Par (Seq (Par (Seq s1 : t1) : s2) : t2),
                Par (Seq (s1 ++ [Par (Seq s2 : t1)]) : t2)
              ]
              | (s1, s2) <- twoWaySplit seqs,
                (t1, t2) <- twoWayPermute ts
            ]

    -- For each pair of proper seq substructures of an arbitrary par structure, splits the first
    -- into 2 (possibly empty) ordered parts ⟨A⟩, ⟨B⟩, the second into similar <C>, <D>, FINISH COMMENT \\\\\\\\\\\\\\\\\\\\\
    twoSeq :: [Term] -> [Term]
    twoSeq ts =
      concat
        [ tseq a b (ts \\ [Seq a, Seq b])
          | (a, b) <- takeTwo (getSeqs ts)
        ]
      where
        tseq :: [Term] -> [Term] -> [Term] -> [Term]
        tseq a b ts =
          [ Par (Seq [Par [Seq a1, Seq b1], Par [Seq a2, Seq b2]] : ts)
            | (a1, a2) <- twoWaySplit a,
              (b1, b2) <- twoWaySplit b
          ]

        takeTwo :: [a] -> [(a, a)]
        takeTwo [] = []
        takeTwo (t : ts) = [(t, t') | t' <- ts] ++ takeTwo ts

    getSeqs :: [Term] -> [[Term]]
    getSeqs [] = []
    getSeqs ((Seq t) : ts) = t : getSeqs ts
    getSeqs (t : ts) = getSeqs ts

-- Generates a list of all possible single step qDown applications of a Term
qUp :: Term -> [Term]
qUp x = case x of
  Seq ts ->
    qp ts ++ nub [preprocess (Seq t) | t <- deepInference ts qUp]
  Par ts -> nub [preprocess (Par t) | t <- deepInference ts qUp]
  Copar ts -> nub [preprocess (Copar t) | t <- deepInference ts qUp]
  t -> []
  where
    qp :: [Term] -> [Term]
    qp ts =
      nub
        ( map
            preprocess
            ( noCopar ts
                ++ oneCopar ts
                ++ twoCopar ts
            )
        )
        \\ [Seq ts]

    noCopar :: [Term] -> [Term]
    noCopar ts =
      concat
        [ [ Seq (a ++ [Copar [Seq b1, Seq b2]] ++ c)
            | (b1, b2) <-
                filter
                  (\(b1, b2) -> not (null b1) && not (null b2))
                  (twoWaySplit b)
          ]
          | (a, b, c) <- threeWaySplit ts
        ]
      where
        -- Splits a list into 3 parts where the middle part has length at least 2
        threeWaySplit :: [a] -> [([a], [a], [a])]
        threeWaySplit ts =
          filter
            (\(a, b, c) -> length b > 1)
            ( concat
                [ [ (take m ts, take n (drop m ts), drop n (drop m ts))
                    | n <- [0 .. length ts - m]
                  ]
                  | m <- [0 .. length ts]
                ]
            )

    oneCopar :: [Term] -> [Term]
    oneCopar ts =
      concat
        [ concat
            [ permuteFirst (a, b1, b2, c) ++ permuteLast (a, b1, b2, c)
              | (b1, b2) <- twoWayPermute b
            ]
          | (a, b, c) <- getCopar ts
        ]
      where
        getCopar :: [Term] -> [([Term], [Term], [Term])]
        getCopar = gCop []
          where
            gCop :: [Term] -> [Term] -> [([Term], [Term], [Term])]
            gCop _ [] = []
            gCop seen (Copar t : ts) = (reverse seen, t, ts) : gCop (Copar t : seen) ts
            gCop seen (t : ts) = gCop (t : seen) ts

        permuteFirst :: ([Term], [Term], [Term], [Term]) -> [Term]
        permuteFirst (a, b1, b2, c) =
          concat
            [ [ Seq (a1 ++ [Copar (b1 ++ [Seq (a2 ++ [Copar b2])])] ++ c),
                Seq (a1 ++ [Copar (Seq (a2 ++ [Copar b1]) : b2)] ++ c)
              ]
              | (a1, a2) <- twoWaySplit a
            ]

        permuteLast :: ([Term], [Term], [Term], [Term]) -> [Term]
        permuteLast (a, b1, b2, c) =
          concat
            [ [ Seq (a ++ [Copar (b1 ++ [Seq (Copar b2 : c1)])] ++ c2),
                Seq (a ++ [Copar (Seq (Copar b1 : c1) : b2)] ++ c2)
              ]
              | (c1, c2) <- twoWaySplit c
            ]

    twoCopar :: [Term] -> [Term]
    twoCopar ts =
      concat
        [ concat
            [ [ Seq (a ++ [Copar [Seq [Copar b1, Copar c1], Seq [Copar b2, Copar c2]]] ++ d)
                | (c1, c2) <- twoWayPermute c
              ]
              | (b1, b2) <- twoWayPermute b
            ]
          | (a, b, c, d) <- consecutiveCopar ts
        ]
      where
        consecutiveCopar :: [Term] -> [([Term], [Term], [Term], [Term])]
        consecutiveCopar = cC [] []
          where
            cC :: [Term] -> [Term] -> [Term] -> [([Term], [Term], [Term], [Term])]
            cC _ _ [] = []
            cC seen [] (Copar t : ts) = cC (Copar t : seen) t ts
            cC seen cpr (Copar t : ts) = (reverse (drop 1 seen), cpr, t, ts) : cC (Copar t : seen) t ts
            cC seen _ (t : ts) = cC (t : seen) [] ts

---------------------------------------------------------------------------------
-----------------------------Proof Search Algorithm------------------------------
---------------------------------------------------------------------------------

-- Finds all single step rewrites of a possible Term, and records which rule was used to get there
reachable :: Node -> [Node]
reachable (t, _) =
  [(t', 'a') | t' <- aiDown t]
    -- ++ [(t', 'A') | t' <- aiUp t]
    ++ [(t', 's') | t' <- switch t]
    ++ [(t', 'Q') | t' <- qUp t]
    ++ [(t', 'q') | t' <- qDown t]

-- Longest allowed chain of rewrites of a candidate proof without an application of aiDown
pVal :: Int
pVal = 3

-- Breadth first proof search algorithm with pruning
search :: Term -> Maybe Proof
search start = loop [[(start, '_')]]
  where
    loop :: [Proof] -> Maybe Proof
    loop frontier
      | null frontier = Nothing
      | any isDone frontier = find isDone frontier
      | otherwise = loop (filter prune lst) -- `dbg` show (length frontier)
      where
        -- Generates next stage in proof search by attaching every rewrite
        -- rule of the topmost stage of a candidate proof to that proof,
        -- for every candidate proof in the frontier
        lst :: [Proof]
        lst = concat [[r : p | r <- reachable (head p)] | p <- frontier]

        isDone :: Proof -> Bool
        isDone p = fst (head p) == O

        -- Attempted proofs that have not applied aiDown in their last
        -- pVal stages are pruned
        prune :: Proof -> Bool
        prune p
          | length p < pVal = True
          | otherwise = 'a' `elem` map snd (take pVal p)

prove :: String -> IO ()
prove structure = do
  putStrLn "Searching for proof..."
  putStrLn (outputProof (search (preprocess (parse structure))))
  putStrLn "Proof search complete"

{-
Testing material

1: [(a,b),-a,-b]
2: [<a;(b,-a)>,-b,a,-a]
3: [<a;(b,c);d>,<[-a,-b];-d>,-c]
4: [c,<-c;[b,(-b,[a,-a])]>]
-}

---------------TESTING FUNCTIONS-----------------
dbg :: a -> String -> a
dbg = flip trace

testEq :: String -> String -> Bool
testEq str1 str2 =
  preprocess (parse str1) == preprocess (parse str2)
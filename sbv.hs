---------------------------------------------------------------------------------
---------------------------Imports and Structures--------------------------------
---------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use head" #-}

import Control.Monad (guard)
import Control.Monad.RWS (gets)
import Data.Char (isLetter)
import Data.List (intercalate, sort, subsequences, (\\))
import Distribution.Simple.Utils (xargs)
import GHC.Exts.Heap (GenClosure (tsoStack))
import Language.Haskell.TH (safe)
import Text.Read (Lexeme (String))

data Term = O | V Char | Seq [Term] | Par [Term] | Copar [Term] | Not Term
  deriving (Eq)

instance Show Term where
  show = outputTerm

---------------------------------------------------------------------------------
---------------------------String Parsing and Outputting-------------------------
---------------------------------------------------------------------------------

-- Parses an input string as an SBV Term
parse :: String -> Term
parse x = case x of
  "O" -> O
  "" -> O
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
oterms :: [Term] -> IO ()
oterms ts = putStrLn (intercalate "\n" [outputTerm t | t <- ts])

-- Outputs the result of a bfs in a more readable way
osearch :: [(Term, String)] -> IO ()
osearch ts = putStrLn (intercalate "\n" [outputTerm t ++ "    {" ++ p ++ "}" | (t, p) <- ts])

---------------------------------------------------------------------------------
---------------------------Normalise Terms---------------------------------------
---------------------------------------------------------------------------------

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

-- Recursively applies de morgan's laws resulting in the only Not terms being variables
deMorgan :: Term -> Term
deMorgan x = case x of
  Not (Seq ts) -> Seq [Not (deMorgan t) | t <- ts]
  Not (Par ts) -> Copar [Not (deMorgan t) | t <- ts]
  Not (Copar ts) -> Par [Not (deMorgan t) | t <- ts]
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

-- Reorders par and copar structures into a predefined normal form
-- (Copar, Par, Seq, Var, Not Var) using sortTerms
reorder :: Term -> Term
reorder x = case x of
  Seq ts -> Seq [reorder t | t <- ts]
  Par ts -> Par [reorder t | t <- sortTerms ts]
  Copar ts -> Copar [reorder t | t <- sortTerms ts]
  t -> t

-- Removes duplicate elements from any list
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates [] = []
removeDuplicates (x : xs) = x : removeDuplicates (filter (/= x) xs)

-- Sorts a list of terms into the normal order
sortTerms :: [Term] -> [Term]
sortTerms ts = removeDuplicates (st [] [] [] [] [] ts)
  where
    st :: [Term] -> [Term] -> [Term] -> [Term] -> [Term] -> [Term] -> [Term]
    st s p c v n x = case x of
      (Seq t : ts) -> st (Seq t : s) p c v n ts
      (Par t : ts) -> st s (Par t : p) c v n ts
      (Copar t : ts) -> st s p (Copar t : c) v n ts
      (V x : ts) -> st s p c (V x : v) n ts
      (Not (V x) : ts) -> st s p c v (Not (V x) : n) ts
      [] -> reverse s ++ reverse p ++ reverse c ++ sortVars v ++ sortVars n
      where
        sortVars :: [Term] -> [Term]
        sortVars (V t : ts) = [V x | x <- sort [x | V x <- V t : ts]]
        sortVars (Not (V t) : ts) = [Not (V x) | x <- sort [x | Not (V x) <- Not (V t) : ts]]
        sortVars [] = []

-- Applies all of the above functions in order to put any term in its normal form
-- Defined such that any 2 logically equivalent terms will be exactly equal once normalised
normalise :: Term -> Term
normalise t = reorder (doubleNegative (associate (extractSingleton (deMorgan (removeId t)))))

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

-- Gets a list of every letter that has been used as a variable in a term
getUsedAtoms :: Term -> [Char]
getUsedAtoms x = case x of
  Seq ts -> removeDuplicates (concat [getUsedAtoms t | t <- ts])
  Par ts -> removeDuplicates (concat [getUsedAtoms t | t <- ts])
  Copar ts -> removeDuplicates (concat [getUsedAtoms t | t <- ts])
  Not (V t) -> [t]
  V t -> [t]
  O -> []

-- Gets the earliest letter in the alphabet that has not been used as a variable in a term
getNextAtom :: Term -> Char
getNextAtom t = x !! 0
  where
    x = ['a' .. 'z'] \\ getUsedAtoms t

-- Removes any [a, Not a] pairs from a Par structure for a specified variable a
aiDown :: Char -> Term -> Term
aiDown a (Par ts) = Par (down 0 [] a ts)
  where
    down :: Int -> [Term] -> Char -> [Term] -> [Term]
    down n rest a ((V x) : ts)
      | x == a = down (n + 1) rest a ts
      | otherwise = down n (V x : rest) a ts
    down n rest a (Not (V x) : ts)
      | x == a = down (n - 1) rest a ts
      | otherwise = down n (Not (V x) : rest) a ts
    down n rest a (t : ts) = down n (t : rest) a ts
    down n rest a []
      | n == 0 = reverse rest
      | n < 0 = sortTerms (reverse rest ++ replicate (-n) (Not (V a)))
      | n > 0 = sortTerms (reverse rest ++ replicate n (V a))
aiDown a t = t

-- Adds a Copar pair (a, Not a) to any Par or Copar term; if term is a Seq, will put this pair in
-- every possible position and return a single Par whose elements are these possible rewrites,
-- which will then be unpacked by the alliUp function that calls it
aiUp :: Char -> Term -> Term
aiUp c t
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
alliDown :: Term -> [Term]
alliDown x = case x of
  Par ts ->
    removeDuplicates
      ( map
          normalise
          ( [aiDown a (Par ts) | a <- getUsedAtoms (Par ts)]
              ++ [Par t | t <- deepInference ts alliDown]
          )
      )
      \\ [Par ts]
  Copar ts -> [Copar t | t <- deepInference ts alliDown]
  Seq ts -> [Seq t | t <- deepInference ts alliDown]
  t -> []

-- Generates a list of all possible aiUp rewrites of a term
alliUp :: Term -> [Term]
alliUp x = case x of
  Seq ts ->
    removeDuplicates
      ( map
          normalise
          ( concat [ts | Par ts <- [aiUp a (Seq ts) | a <- getUsedAtoms (Seq ts)]]
              ++ [Seq t | t <- deepInference ts alliUp]
          )
      )
      \\ [Seq ts]
  Par ts ->
    removeDuplicates
      ( map
          normalise
          ( [aiUp a (Par ts) | a <- getUsedAtoms (Par ts)]
              ++ [Par t | t <- deepInference ts alliUp]
          )
      )
      \\ [Par ts]
  Copar ts ->
    removeDuplicates
      ( map
          normalise
          ( [aiUp a (Copar ts) | a <- getUsedAtoms (Copar ts)]
              ++ [Copar t | t <- deepInference ts alliUp]
          )
      )
      \\ [Copar ts]
  t -> []

-- Generates a list of all possible single step switches of a term
switch :: Term -> [Term]
switch x = case x of
  Par ts ->
    removeDuplicates
      ( map
          normalise
          ( [Par t | t <- uncurry permute (extractCopar ts)]
              ++ [Par t | t <- deepInference ts switch]
          )
      )
      \\ [Par ts] -- Switches subterms
  Copar ts -> [normalise (Copar t) | t <- deepInference ts switch]
  Seq ts -> [normalise (Seq t) | t <- deepInference ts switch]
  t -> []
  where
    -- If a list of terms has a copar element, returns ([the terms within the copar],[other elements of list])
    extractCopar :: [Term] -> ([Term], [Term])
    extractCopar = ec []
      where
        ec :: [Term] -> [Term] -> ([Term], [Term])
        ec as (Copar ts : bs) = (ts, reverse as ++ bs)
        ec as (x : bs) = ec (x : as) bs
        ec as [] = ([], reverse as)

    permute :: [Term] -> [Term] -> [[Term]] -- Alter this part to avoid incorrect permutations
    permute [] bs = []
    permute as bs =
      [ Copar (Par (Copar a : b) : (as \\ a)) : (bs \\ b)
        | a <- powerset as,
          b <- powerset bs
      ]

    powerset :: [a] -> [[a]]
    powerset [] = [[]]
    powerset (x : xs) = [x : ps | ps <- powerset xs] ++ powerset xs

-- Generates a list of all possible single step qDown applications of a term
qDown :: Term -> [Term]
qDown x = case x of
  Par ts ->
    removeDuplicates
      ( map
          normalise
          ( [Seq t | t <- uncurry permute (extractSeq ts)]
              ++ [Par t | t <- deepInference ts qDown]
          )
      )
      \\ [Par ts]
  Copar ts -> [normalise (Copar t) | t <- deepInference ts qDown]
  Seq ts -> [normalise (Seq t) | t <- deepInference ts qDown]
  t -> []
  where
    -- Returns a list of all sublists that begin with the first element
    getSublists :: [a] -> [[a]]
    getSublists [] = []
    getSublists (x : xs) = [x] : [x : ys | ys <- getSublists xs]

    -- Given a list of terms, returns ([],[]) unless the list is precicely 2 Seq structures
    -- and nothing more, in which case it returns ([terms in first Seq], [terms in second Seq])
    extractSeq :: [Term] -> ([Term], [Term])
    extractSeq = es [] []
      where
        es :: [Term] -> [Term] -> [Term] -> ([Term], [Term])
        es [] [] (Seq ts : rest) = es ts [] rest
        es first [] (Seq ts : rest) = es first ts rest
        es first second [] = (first, second)
        es _ _ t = ([], [])

    permute :: [Term] -> [Term] -> [[Term]]
    permute [] [] = []
    permute as bs =
      [ [Par [Seq a, Seq b], Par [Seq (as \\ a), Seq (bs \\ b)]]
        | a <- getSublists as,
          b <- getSublists bs
      ]

-- Generates a list of all possible single step qUp applications of a term
qUp :: Term -> [Term]
qUp x = case x of
  Seq ts ->
    removeDuplicates
      ( map
          normalise
          ( [Copar t | t <- uncurry permute (extractCopar ts)]
              ++ [Seq t | t <- deepInference ts qUp]
          )
      )
      \\ [Seq ts]
  Copar ts -> [normalise (Copar t) | t <- deepInference ts qUp]
  Par ts -> [normalise (Par t) | t <- deepInference ts qUp]
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

reachable :: (Term, String) -> [(Term, String)]
reachable (t, p) =
  [(ts, p' ++ "ai-") | ts <- alliDown t]
    ++ [(ts, p' ++ "ai+") | ts <- alliUp t]
    ++ [(ts, p' ++ "s") | ts <- switch t]
    ++ [(ts, p' ++ "q-") | ts <- qDown t]
    ++ [(ts, p' ++ "q+") | ts <- qUp t]
  where
    p' :: String
    p'
      | p == "" = ""
      | otherwise = p ++ ", "

---------------------------------------------------------------------------------
-----------------------------Proof Search Algorithm------------------------------
---------------------------------------------------------------------------------

-- Searches for a proof of a given term that can be reached within a specified number of rewrites
bfs :: Term -> Int -> IO ()
bfs t n = osearch (concat [doBfs [] (t, "") n' | n' <- [0 .. n]])
  where
    -- t is current term, p is path from given term to t
    doBfs :: [Term] -> (Term, String) -> Int -> [(Term, String)]
    doBfs seen (t, p) 0
      | t `elem` seen = []
      | otherwise = [(t, p)]
    doBfs seen (t, p) k =
      reachable (t, p) >>= \(t', p') ->
        guard (t' `notElem` seen)
          >> doBfs (t : seen) (t', p') (k - 1)
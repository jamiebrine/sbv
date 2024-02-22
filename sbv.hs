---------------------------------------------------------------------------------
---------------------------Imports and Structures--------------------------------
---------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use infix" #-}

import Data.Char (isLetter)
import Data.List (intercalate, sort, (\\))
import Distribution.Simple.Utils (xargs)
import GHC.Exts.Heap (GenClosure (tsoStack))
import Language.Haskell.TH (safe)

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

---------------------------------------------------------------------------------
---------------------------Normalise Terms---------------------------------------
---------------------------------------------------------------------------------

-- Removes any lone O terms from inside a Seq, Par, or Copar
removeId :: Term -> Term
removeId x = case x of
  Seq ts -> Seq (rmv [] ts)
  Par ts -> Par (rmv [] ts)
  Copar ts -> Copar (rmv [] ts)
  Not ts -> Not (removeId ts)
  t -> t
  where
    rmv :: [Term] -> [Term] -> [Term]
    rmv kept (O : ts) = rmv kept ts
    rmv kept (t : ts) = rmv (removeId t : kept) ts
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

-- Reorders par and copar structures into a predefined normal form (Copar, Par, Seq, Var, Not Var) using sortTerms
reorder :: Term -> Term
reorder x = case x of
  Seq ts -> Seq [reorder t | t <- ts]
  Par ts -> Par [reorder t | t <- sortTerms ts]
  Copar ts -> Copar [reorder t | t <- sortTerms ts]
  t -> t

-- Sorts a list of terms into the normal order
sortTerms :: [Term] -> [Term]
sortTerms = st [] [] [] [] []
  where
    st :: [Term] -> [Term] -> [Term] -> [Term] -> [Term] -> [Term] -> [Term]
    st s p c v n x = case x of
      (Seq t : ts) -> st (Seq t : s) p c v n ts
      (Par t : ts) -> st s (Par t : p) c v n ts
      (Copar t : ts) -> st s p (Copar t : c) v n ts
      (V x : ts) -> st s p c (V x : v) n ts
      (Not (V x) : ts) -> st s p c v (Not (V x) : n) ts
      [] -> s ++ p ++ c ++ sortVars v ++ sortVars n
      where
        sortVars :: [Term] -> [Term]
        sortVars (V t : ts) = [V x | x <- sort [x | V x <- V t : ts]]
        sortVars (Not (V t) : ts) = [Not (V x) | x <- sort [x | Not (V x) <- Not (V t) : ts]]
        sortVars [] = []

-- Applies all of the above functions in order to put any term in its normal form
-- This form is defined in such a way that any 2 logically equivalent terms will be exactly equal once normalised
normalise :: Term -> Term
normalise t = reorder (extractSingleton (doubleNegative (associate (deMorgan (removeId t)))))

---------------------------------------------------------------------------------
-----------------------------Rewrite Rules---------------------------------------
---------------------------------------------------------------------------------

-- Helper function for rewrites that generate lists of terms
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates [] = []
removeDuplicates (x : xs) = x : removeDuplicates (filter (/= x) xs)

-- Removes any [a, Not a] pairs from a Par structure for a specified variable a
aiDown :: Char -> Term -> Term
aiDown a (Par ts) = Par (annihilate 0 [] a ts)
  where
    annihilate :: Int -> [Term] -> Char -> [Term] -> [Term]
    annihilate n rest a ((V x) : ts)
      | x == a = annihilate (n + 1) rest a ts
      | otherwise = annihilate n (V x : rest) a ts
    annihilate n rest a (Not (V x) : ts)
      | x == a = annihilate (n - 1) rest a ts
      | otherwise = annihilate n (Not (V x) : rest) a ts
    annihilate n rest a (t : ts) = annihilate n (t : rest) a ts
    annihilate n rest a []
      | n == 0 = reverse rest
      | n < 0 = sortTerms (reverse rest ++ replicate (-n) (Not (V a)))
      | n > 0 = sortTerms (reverse rest ++ replicate n (V a))
aiDown a t = t

-- Generates a list of all possible aiDown rewrites of a term
alliDown :: Term -> [Term]
alliDown t = removeDuplicates [aiDown a t | a <- ['a' .. 'z']]

-- Adds a Copar pair (a, Not a) to any term
aiUp :: Char -> Term -> Term
aiUp c t
  | not (isLetter c && c > 'Z') = error "Invalid rewrite - Variables must be lowercase letters only"
  | otherwise = normalise (up c t)
  where
    up :: Char -> Term -> Term
    up c (Seq ts) = Seq (ts ++ [Copar [V c, Not (V c)]])
    up c (Par ts) = Par (ts ++ [Copar [V c, Not (V c)]])
    up c (Copar ts) = Copar (ts ++ [Copar [V c, Not (V c)]])

-- Generates a list of all possible aiUp rewrites of a term
alliUp :: Term -> [Term]
alliUp t = removeDuplicates [aiUp a t | a <- ['a' .. 'z']]

-- Generates a list of all possible single step switches of a term
switch :: Term -> [Term]
switch x = case x of
  Par ts ->
    removeDuplicates [normalise (Copar t) | t <- uncurry permute (extractCopar [] ts)] -- Switches top level term
      ++ [normalise (Par t) | t <- deepSwitch ts] -- Switches subterms
  Copar ts -> [normalise (Copar t) | t <- deepSwitch ts]
  Seq ts -> [normalise (Seq t) | t <- deepSwitch ts]
  t -> []
  where
    -- If a list of terms has a copar element, returns ([the terms within the copar],[other elements of list])
    extractCopar :: [Term] -> [Term] -> ([Term], [Term])
    extractCopar as (Copar ts : bs) = (ts, reverse as ++ bs)
    extractCopar as (x : bs) = extractCopar (x : as) bs
    extractCopar as [] = ([], reverse as)

    permute :: [Term] -> [Term] -> [[Term]] -- Alter this part to avoid incorrect permutations
    permute [] bs = []
    permute as bs =
      [ sortTerms (Par (sortTerms (a ++ (bs \\ b))) : b ++ (as \\ a))
        | a <- powerset as,
          b <- powerset bs
      ]

    powerset :: [a] -> [[a]]
    powerset [] = [[]]
    powerset (x : xs) = [x : ps | ps <- powerset xs] ++ powerset xs

    -- Switches each term in a list, returning a list of lists in which one term at a time are switched
    -- and the others are unchanged
    deepSwitch :: [Term] -> [[Term]]
    deepSwitch = ds []
      where
        ds :: [Term] -> [Term] -> [[Term]]
        ds seen [] = []
        ds seen (t : ts) = [reverse seen ++ [s] ++ ts | s <- switch t] ++ ds (t : seen) ts

qDown :: Term -> [Term]
qDown x = case x of
  _ -> []

qUp :: Term -> [Term]
qUp x = case x of
  _ -> []
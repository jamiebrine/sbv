---------------------------------------------------------------------------------
---------------------------Imports and Structures--------------------------------
---------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use infix" #-}

import Data.Char
import Data.List
import Distribution.Simple.Utils (xargs)
import GHC.Exts.Heap (GenClosure (tsoStack))
import Language.Haskell.TH (safe)

data Term = O | V Char | Seq [Term] | Par [Term] | Copar [Term] | Not Term
  deriving (Eq)

instance Show Term where
  show = outputTerm

---------------------------------------------------------------------------------
---------------------------String Parsing Functions------------------------------
---------------------------------------------------------------------------------

-- Checks that a character is a lowercase letter and not the O symbol (reserved for identity)
isVariableChar :: Char -> Bool
isVariableChar c = isLetter c && (c > 'Z')

-- Removes last character of a string
trim :: String -> String
trim [] = error "Empty String"
trim [x] = []
trim (x : xs) = x : trim xs

-- Main parsing function, using 4 below helper functions to handle each
parse :: String -> Term
parse "O" = O
parse "" = O
parse (x : "")
  | isVariableChar x = V x
  | otherwise = error "Invalid expression - variables should be lowercase letters only"
parse ('{' : xs) = parseNot (parse (trim xs))
parse ('<' : xs) = parseSeq 0 [] [] xs
parse ('[' : xs) = parsePar 0 [] [] xs
parse ('(' : xs) = parseCopar 0 [] [] xs
parse str = error "Invalid expression - invalid sequence of characters"

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

---------------------------------------------------------------------------------
---------------------------Term Outputting Functions-----------------------------
---------------------------------------------------------------------------------

-- Outputs a term as a string, acting as a logical inverse to the parse function
outputTerm :: Term -> String
outputTerm O = "O"
outputTerm (V x) = x : ""
outputTerm (Not x) = "{" ++ outputTerm x ++ "}"
outputTerm (Seq xs) = "<" ++ intercalate ";" [outputTerm x | x <- xs] ++ ">"
outputTerm (Par xs) = "[" ++ intercalate "," [outputTerm x | x <- xs] ++ "]"
outputTerm (Copar xs) = "(" ++ intercalate "," [outputTerm x | x <- xs] ++ ")"

-- Outputs a list of terms, each on a new line
outputTerms :: [Term] -> String
outputTerms (t : ts) = outputTerm t ++ "\n" ++ outputTerms ts
outputTerms [] = ""

---------------------------------------------------------------------------------
---------------------------Normalise Terms---------------------------------------
---------------------------------------------------------------------------------

-- Removes any lone O terms from inside a Seq, Par, or Copar
removeId :: Term -> Term
removeId (Seq ts) = Seq (rmv [] ts)
removeId (Par ts) = Par (rmv [] ts)
removeId (Copar ts) = Copar (rmv [] ts)
removeId (Not ts) = Not (removeId ts)
removeId t = t

-- Helper function that removes any O from a list of terms
rmv :: [Term] -> [Term] -> [Term]
rmv kept (O : ts) = rmv kept ts
rmv kept (t : ts) = rmv (removeId t : kept) ts
rmv kept [] = reverse kept

-- Recursively applies de morgan's laws resulting in the only Not terms being variables
deMorgan :: Term -> Term
deMorgan (Not (Seq ts)) = Seq [Not (deMorgan t) | t <- ts]
deMorgan (Not (Par ts)) = Copar [Not (deMorgan t) | t <- ts]
deMorgan (Not (Copar ts)) = Par [Not (deMorgan t) | t <- ts]
deMorgan (Seq ts) = Seq [deMorgan t | t <- ts]
deMorgan (Par ts) = Par [deMorgan t | t <- ts]
deMorgan (Copar ts) = Copar [deMorgan t | t <- ts]
deMorgan t = t

-- Flattens instances of a structure nested within the same structure
associate :: Term -> Term
associate (Seq ts) = Seq (concat [unSeq t | t <- ts])
associate (Par ts) = Par (concat [unPar t | t <- ts])
associate (Copar ts) = Copar (concat [unCopar t | t <- ts])
associate t = t

-- Flattening helper functions
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
doubleNegative (Not (Not t)) = doubleNegative t
doubleNegative (Seq ts) = Seq [doubleNegative t | t <- ts]
doubleNegative (Par ts) = Par [doubleNegative t | t <- ts]
doubleNegative (Copar ts) = Copar [doubleNegative t | t <- ts]
doubleNegative t = t

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

-- Reorders par and copar structures into a predefined normal form (Copar, Par, Seq, Var, Not Var)
reorder :: Term -> Term
reorder (Seq ts) = Seq [reorder t | t <- ts]
reorder (Par ts) = Par [reorder t | t <- sortTerms [] [] [] [] [] ts]
reorder (Copar ts) = Copar [reorder t | t <- sortTerms [] [] [] [] [] ts]
reorder t = t

-- Helper function for reorder that collects like terms and then concatenates
sortTerms :: [Term] -> [Term] -> [Term] -> [Term] -> [Term] -> [Term] -> [Term]
sortTerms s p c v n (Seq t : ts) = sortTerms (Seq t : s) p c v n ts
sortTerms s p c v n (Par t : ts) = sortTerms s (Par t : p) c v n ts
sortTerms s p c v n (Copar t : ts) = sortTerms s p (Copar t : c) v n ts
sortTerms s p c v n (V x : ts) = sortTerms s p c (V x : v) n ts
sortTerms s p c v n (Not (V x) : ts) = sortTerms s p c v (Not (V x) : n) ts
sortTerms s p c v n [] = reverse c ++ reverse p ++ reverse p ++ sortVars v ++ sortVars n

-- Helper function to sort a list of variables (or Not variables) alphabetically
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
      | n < 0 = sortTerms [] [] [] [] [] (reverse rest ++ replicate (-n) (Not (V a)))
      | n > 0 = sortTerms [] [] [] [] [] (reverse rest ++ replicate n (V a))
aiDown a t = t

-- Adds a Copar pair (a, Not a) to any term
aiUp :: Char -> Term -> Term
aiUp c t
  | not (isVariableChar c) = error "Invalid rewrite - Variables must be lowercase letters only"
  | otherwise = normalise (up c t)
  where
    up :: Char -> Term -> Term
    up c (Seq ts) = Seq (ts ++ [Copar [V c, Not (V c)]])
    up c (Par ts) = Par (ts ++ [Copar [V c, Not (V c)]])
    up c (Copar ts) = Copar (ts ++ [Copar [V c, Not (V c)]])

-- Generates a list of all possible permutations of a Par term with a Copar element
switch :: Term -> [Term]
switch (Par ts) = [] -- Need Par (as ++ Copar ts ++ bs) to then pass (as ++ bs) ts to permute
switch t = [t]

permute :: [Term] -> [Term] -> [[Term]]
permute as bs = []

powerset :: [a] -> [[a]]
powerset [] = []
powerset (x : xs) = [x : ps | ps <- powerset xs] ++ powerset xs

complement :: (Foldable t, Eq a) => t a -> [a] -> [a]
complement lst = filter (`notElem` lst)
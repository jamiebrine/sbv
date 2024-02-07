{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
import Distribution.Simple.Utils (xargs)
import Language.Haskell.TH (safe)
import Data.List

--data Term = O | V Char | Seq (Term, Term) | Par (Term, Term) | Copar (Term, Term) | Not Term
--  deriving Show

data Term = O | V Char | Seq [Term] | Par [Term] | Copar [Term] | Not Term
    deriving (Show, Eq)

isVariableChar :: Char -> Bool
isVariableChar c = notElem c "O;,<>[]()'"

trim :: String -> String
trim [] = error "Empty String"
trim [x] = []
trim (x:xs) = x:trim xs

parse :: String -> Term
parse "O"            = O
parse ""             = O
parse (x:"")
  | isVariableChar x = V x
  | otherwise        = error "Invalid expression - variables should be letters only"
parse ('{':xs)       = Not (parse (trim xs))
parse ('<':xs)       = parseSeq 0 [] [] xs
parse ('[':xs)       = parsePar 0 [] [] xs
parse ('(':xs)       = parseCopar 0 [] [] xs
parse str            = error "Invalid expression - invalid sequence of characters. Have you closed your brackets?"

-- Int value handles layers of nested seqs
parseSeq :: Int -> [Term] -> [Char] -> String -> Term
parseSeq 0 ts ys (x:xs)
  | x == '<'  = parseSeq 1 ts (x:ys) xs
  | x == '>'  = Seq (reverse (parse (reverse ys) : ts))
  | x == ';'  = parseSeq 0 (parse (reverse ys) : ts) [] xs
  | otherwise = parseSeq 0 ts (x:ys) xs
parseSeq n ts ys (x:xs)
  | x == '>'  = parseSeq (n-1) ts (x:ys) xs
  | x == '<'  = parseSeq (n+1) ts (x:ys) xs
  | otherwise = parseSeq n ts (x:ys) xs

parsePar :: Int -> [Term] -> [Char] -> String -> Term
parsePar 0 ts ys (x:xs)
  | x == '('  = parsePar 1 ts (x:ys) xs
  | x == '['  = parsePar 1 ts (x:ys) xs
  | x == ']'  = Par (reverse (parse (reverse ys) : ts))
  | x == ','  = parsePar 0 (parse (reverse ys) : ts) [] xs
  | otherwise = parsePar 0 ts (x:ys) xs
parsePar n ts ys (x:xs)
  | x == ')'  = parsePar (n-1) ts (x:ys) xs
  | x == ']'  = parsePar (n-1) ts (x:ys) xs
  | x == '('  = parsePar (n+1) ts (x:ys) xs
  | x == '['  = parsePar (n+1) ts (x:ys) xs
  | otherwise = parsePar n ts (x:ys) xs

parseCopar :: Int -> [Term] -> [Char] -> String -> Term
parseCopar 0 ts ys (x:xs)
  | x == '('  = parseCopar 1 ts (x:ys) xs
  | x == '['  = parseCopar 1 ts (x:ys) xs
  | x == ')'  = Copar (reverse (parse (reverse ys) : ts))
  | x == ','  = parseCopar 0 (parse (reverse ys) : ts) [] xs
  | otherwise = parseCopar 0 ts (x:ys) xs
parseCopar n ts ys (x:xs)
  | x == ')'  = parseCopar (n-1) ts (x:ys) xs
  | x == ']'  = parseCopar (n-1) ts (x:ys) xs
  | x == '('  = parseCopar (n+1) ts (x:ys) xs
  | x == '['  = parseCopar (n+1) ts (x:ys) xs
  | otherwise = parseCopar n ts (x:ys) xs

outputTerm :: Term -> String
outputTerm O = "O"
outputTerm (V x) = x : ""
outputTerm (Not x) = "{" ++ outputTerm x ++ "}"
outputTerm (Seq xs) = "<" ++ intercalate ";" [outputTerm x | x <- xs] ++ ">"
outputTerm (Par xs) = "[" ++ intercalate "," [outputTerm x | x <- xs] ++ "]"
outputTerm (Copar xs) = "(" ++ intercalate "," [outputTerm x | x <- xs] ++ ")"
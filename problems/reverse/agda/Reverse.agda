-- List reverse with proof that reverse is involutive: reverse (reverse xs) ≡ xs.
-- Uses propositional equality and structural induction.

module Reverse where

open import Agda.Builtin.List
open import Agda.Builtin.Equality

-- Append (++) -- not a builtin, so we define it here.
infixr 5 _++_
_++_ : {A : Set} -> List A -> List A -> List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Standard naive reverse: O(n²) but easy to reason about.
reverse : {A : Set} -> List A -> List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

-- Lemma: ++ is associative.
++-assoc : {A : Set} (xs ys zs : List A)
         -> (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

-- Lemma: xs ++ [] ≡ xs.
++-[] : {A : Set} (xs : List A) -> xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) rewrite ++-[] xs = refl

-- Lemma: reverse distributes over append (with a flip).
reverse-++ : {A : Set} (xs ys : List A)
           -> reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ []       ys rewrite ++-[] (reverse ys) = refl
reverse-++ (x ∷ xs) ys rewrite reverse-++ xs ys
                              | ++-assoc (reverse ys) (reverse xs) (x ∷ [])
                              = refl

-- Theorem: reverse is its own inverse.
reverse-reverse : {A : Set} (xs : List A) -> reverse (reverse xs) ≡ xs
reverse-reverse []       = refl
reverse-reverse (x ∷ xs) rewrite reverse-++ (reverse xs) (x ∷ [])
                                | reverse-reverse xs
                                = refl

-- Executable entry point.
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Nat
open import Agda.Builtin.String

postulate
  showList    : List Nat -> String
  putStrLn    : String -> IO ⊤
{-# COMPILE JS showList = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; } #-}
{-# COMPILE JS putStrLn = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (showList (reverse (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])))

-- Insertion sort with a sortedness proof.
-- Sortedness is a *type-level* predicate; the proof is a constructive term
-- that the type checker verifies as well-formed.

module InsertionSort where

open import Agda.Builtin.Nat
open import Agda.Builtin.List

-- ≤ on naturals as an inductive family.
data _≤_ : Nat -> Nat -> Set where
  z≤n : {n : Nat}             -> zero ≤ n
  s≤s : {m n : Nat} -> m ≤ n  -> suc m ≤ suc n

-- ≤ is transitive.
≤-trans : {a b c : Nat} -> a ≤ b -> b ≤ c -> a ≤ c
≤-trans z≤n       _         = z≤n
≤-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤-trans a≤b b≤c)

-- A decidable comparison: either x ≤ y, or y ≤ x.
data Order (x y : Nat) : Set where
  le : x ≤ y -> Order x y
  gt : y ≤ x -> Order x y

compare : (x y : Nat) -> Order x y
compare zero    y       = le z≤n
compare (suc x) zero    = gt z≤n
compare (suc x) (suc y) with compare x y
... | le p = le (s≤s p)
... | gt p = gt (s≤s p)

-- Predicate "x is ≤ every element of xs".
data _≤*_ (x : Nat) : List Nat -> Set where
  []  : x ≤* []
  _∷_ : {y : Nat} {ys : List Nat} -> x ≤ y -> x ≤* ys -> x ≤* (y ∷ ys)

-- Sortedness as an inductive proposition.
data Sorted : List Nat -> Set where
  []  : Sorted []
  _∷_ : {x : Nat} {xs : List Nat} -> x ≤* xs -> Sorted xs -> Sorted (x ∷ xs)

-- If x ≤ y and y is below all of xs, then x is below all of xs.
≤*-trans : {x y : Nat} {xs : List Nat} -> x ≤ y -> y ≤* xs -> x ≤* xs
≤*-trans x≤y []             = []
≤*-trans x≤y (y≤z ∷ y≤*rest) = ≤-trans x≤y y≤z ∷ ≤*-trans x≤y y≤*rest

-- Insertion into a list (no proof obligation at the value level).
insert : Nat -> List Nat -> List Nat
insert x []       = x ∷ []
insert x (y ∷ ys) with compare x y
... | le _ = x ∷ y ∷ ys
... | gt _ = y ∷ insert x ys

-- Lemma: insert preserves the "lo ≤ every elem" predicate.
insert-≤* : {lo x : Nat} {xs : List Nat}
          -> lo ≤ x -> lo ≤* xs -> lo ≤* insert x xs
insert-≤* {lo} {x} {[]}     lo≤x []                = lo≤x ∷ []
insert-≤* {lo} {x} {y ∷ ys} lo≤x (lo≤y ∷ lo≤*rest) with compare x y
... | le _ = lo≤x ∷ lo≤y ∷ lo≤*rest
... | gt _ = lo≤y ∷ insert-≤* lo≤x lo≤*rest

-- Theorem: insert preserves sortedness.
insert-sorted : (x : Nat) (xs : List Nat) -> Sorted xs -> Sorted (insert x xs)
insert-sorted x []       []                = [] ∷ []
insert-sorted x (y ∷ ys) (y≤*ys ∷ s-ys) with compare x y
... | le x≤y = (x≤y ∷ ≤*-trans x≤y y≤*ys) ∷ (y≤*ys ∷ s-ys)
... | gt y≤x = insert-≤* y≤x y≤*ys ∷ insert-sorted x ys s-ys

-- The sort function.
sort : List Nat -> List Nat
sort []       = []
sort (x ∷ xs) = insert x (sort xs)

-- Theorem: sort always returns a sorted list.
sort-sorted : (xs : List Nat) -> Sorted (sort xs)
sort-sorted []       = []
sort-sorted (x ∷ xs) = insert-sorted x (sort xs) (sort-sorted xs)

-- Executable main.
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

postulate
  showList : List Nat -> String
  putStrLn : String -> IO ⊤
{-# COMPILE JS showList = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; } #-}
{-# COMPILE JS putStrLn = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (showList (sort (3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 9 ∷ 2 ∷ 6 ∷ [])))

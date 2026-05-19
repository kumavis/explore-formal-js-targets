-- Length-indexed vectors and zipWith.
-- The type `Vec A n` carries the length as a type-level Nat, so the
-- zipWith function has no "lengths don't match" case to handle — the
-- type system has already eliminated that possibility.

module VecZipWith where

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat -> Set where
  []  : Vec A 0
  _∷_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 5 _∷_

-- Note the type: both inputs and the output share the same length n.
-- The four-case pattern match is exhaustive precisely because Vec's
-- indices rule out the (cons, nil) and (nil, cons) cases.
zipWith : {A B C : Set} {n : Nat} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWith f []       []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

-- A few small sample vectors and the result of zipWith (+).
xs : Vec Nat 3
xs = 1 ∷ 2 ∷ 3 ∷ []

ys : Vec Nat 3
ys = 10 ∷ 20 ∷ 30 ∷ []

result : Vec Nat 3
result = zipWith (\ a b -> a + b) xs ys

-- Executable entry point.  We import List qualified as `L` so its `_∷_`
-- doesn't fight with the Vec `_∷_` constructor.
open import Agda.Builtin.List as L using (List)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

vecToList : {A : Set} {n : Nat} -> Vec A n -> List A
vecToList []       = L.[]
vecToList (x ∷ xs) = x L.∷ vecToList xs

postulate
  showList : List Nat -> String
  putStrLn : String -> IO ⊤
{-# COMPILE JS showList = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; } #-}
{-# COMPILE JS putStrLn = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (showList (vecToList result))

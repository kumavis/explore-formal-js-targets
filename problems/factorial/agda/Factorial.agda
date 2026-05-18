-- Factorial with a proof that the result is always at least 1.
-- The proof is a separate term inhabiting a propositional type.

module Factorial where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- The function itself.
factorial : Nat -> Nat
factorial zero    = 1
factorial (suc n) = (suc n) * factorial n

-- Witness that a Nat is a successor (i.e. >= 1).
data IsPositive : Nat -> Set where
  pos : (n : Nat) -> IsPositive (suc n)

-- Lemma: the product of two positives is positive.
mul-pos : (a b : Nat) -> IsPositive a -> IsPositive b -> IsPositive (a * b)
mul-pos (suc a) (suc b) (pos _) (pos _) = pos _

-- The theorem: factorial n is always positive.
factorial-pos : (n : Nat) -> IsPositive (factorial n)
factorial-pos zero    = pos 0
factorial-pos (suc n) = mul-pos (suc n) (factorial n) (pos n) (factorial-pos n)

-- An executable entry point printing factorial 5.
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate
  natToString : Nat -> String
  putStrLn    : String -> IO ⊤
{-# COMPILE JS natToString = function (n) { return n.toString(); } #-}
{-# COMPILE JS putStrLn    = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (natToString (factorial 5))

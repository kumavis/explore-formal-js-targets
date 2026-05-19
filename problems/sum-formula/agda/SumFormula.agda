-- Triangular-number closed form: sum(0..n) + sum(0..n) ≡ n * (n + 1).
--
-- Agda's nixpkgs install ships only Agda.Builtin (no Data.Nat.Properties),
-- so every algebraic identity that Dafny's SMT solver discharges silently
-- has to be proved here by structural induction. The chain is:
--
--   sym, +-zero, +-suc, +-comm, +-assoc, *-suc, *-comm,
--   then the closed-form theorem itself.

module SumFormula where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- --- Tiny equality kit (sym + equational reasoning combinators) ------------

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

-- --- Addition lemmas -------------------------------------------------------

+-zero : (n : Nat) -> n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) rewrite +-zero n = refl

+-suc : (n m : Nat) -> n + suc m ≡ suc (n + m)
+-suc zero    m = refl
+-suc (suc n) m rewrite +-suc n m = refl

+-comm : (n m : Nat) -> n + m ≡ m + n
+-comm zero    m rewrite +-zero m = refl
+-comm (suc n) m rewrite +-suc m n | +-comm n m = refl

+-assoc : (n m k : Nat) -> (n + m) + k ≡ n + (m + k)
+-assoc zero    m k = refl
+-assoc (suc n) m k rewrite +-assoc n m k = refl

-- --- Multiplication lemmas -------------------------------------------------

*-zero : (n : Nat) -> n * 0 ≡ 0
*-zero zero    = refl
*-zero (suc n) rewrite *-zero n = refl

*-suc : (n m : Nat) -> n * suc m ≡ n + n * m
*-suc zero    m = refl
*-suc (suc n) m
  rewrite *-suc n m
        | sym (+-assoc m n (n * m))
        | +-comm m n
        | +-assoc n m (n * m)
        = refl

*-comm : (n m : Nat) -> n * m ≡ m * n
*-comm zero    m rewrite *-zero m = refl
*-comm (suc n) m rewrite *-suc m n | *-comm n m = refl

-- --- The function and theorem ----------------------------------------------

sum : Nat -> Nat
sum zero    = 0
sum (suc n) = suc n + sum n

-- Useful re-association lemma the closed-form proof needs.
-- (a + b) + (c + d) ≡ a + (c + (b + d))
shuffle : (a b c d : Nat) -> (a + b) + (c + d) ≡ a + (c + (b + d))
shuffle a b c d =
  trans (+-assoc a b (c + d))
  (cong (a +_)
    (trans (sym (+-assoc b c d))
    (trans (cong (_+ d) (+-comm b c))
           (+-assoc c b d))))

closedForm : (n : Nat) -> sum n + sum n ≡ n * suc n
closedForm zero = refl
closedForm (suc n)
  -- After `shuffle` and IH, LHS becomes
  --   suc n + (suc n + n * suc n)
  -- which definitionally equals suc (suc (n + (n + n * suc n))).
  -- The RHS suc n * suc (suc n) unfolds to suc (suc (n + n * suc (suc n))),
  -- and *-suc lets us rewrite n * suc (suc n) into n + n * suc n
  -- so both sides agree.
  rewrite shuffle (suc n) (sum n) (suc n) (sum n)
        | closedForm n
        | *-suc n (suc n)
        | +-suc n (n + n * suc n)
        = refl

-- --- Executable entry point -------------------------------------------------

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

postulate
  natToString : Nat -> String
  putStrLn    : String -> IO ⊤
{-# COMPILE JS natToString = function (n) { return n.toString(); } #-}
{-# COMPILE JS putStrLn    = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

infixr 5 _++_
_++_ : String -> String -> String
s ++ t = primStringAppend s t

main : IO ⊤
main = putStrLn (
    "sum(0..10) = "      ++ natToString (sum 10) ++
    "  (sum+sum = "      ++ natToString (sum 10 + sum 10) ++
    ", n*(n+1) = "       ++ natToString (10 * 11) ++ ")"
  )

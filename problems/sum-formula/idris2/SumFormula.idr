||| Triangular-number closed form: 2 * sum(0..n) = n * (n + 1).
|||
||| Idris2 has no SMT backend, so the algebra is *manual*: every step
||| where Dafny waves its hand at nonlinear arithmetic becomes an explicit
||| chain of rewrites using lemmas from `Data.Nat`.

module SumFormula

import Data.Nat
import Data.Nat.Views

%default total

sum : Nat -> Nat
sum Z     = 0
sum (S n) = (S n) + sum n

-- Goal: 2 * sum n = n * (S n)
--
-- Inductive step on (S n):
--   2 * sum (S n)
--     = 2 * (S n + sum n)                      [def of sum]
--     = 2 * S n + 2 * sum n                    [left distrib]
--     = 2 * S n + n * S n                      [IH]
--     = (2 + n) * S n                          [right distrib backwards]
--     = S (S n) * S n                          [def of +]
--     = S n * S (S n)                          [* commutativity]

closedForm : (n : Nat) -> 2 * sum n = n * (S n)
closedForm Z = Refl
closedForm (S n) =
  let ih = closedForm n in
  rewrite multDistributesOverPlusRight 2 (S n) (sum n) in
  rewrite ih in
  rewrite sym (multDistributesOverPlusLeft 2 n (S n)) in
  rewrite multCommutative (2 + n) (S n) in
  Refl

main : IO ()
main = do
  let n = 10
  let s = SumFormula.sum n
  putStrLn ("sum(0..10) = " ++ show s ++ "  (2*sum = " ++ show (2 * s) ++ ", n*(n+1) = " ++ show (n * (n + 1)) ++ ")")

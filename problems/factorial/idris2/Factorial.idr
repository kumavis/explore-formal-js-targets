||| Factorial with a proof that the result is always a successor (>= 1).
||| The proof is a dependently-typed term that Idris2 checks at compile time.

module Factorial

%default total

factorial : Nat -> Nat
factorial Z     = 1
factorial (S n) = (S n) * factorial n

-- Theorem: factorial n is always a successor.
-- Returned as a dependent pair (k ** factorial n = S k).
factorialPos : (n : Nat) -> (k : Nat ** factorial n = S k)
factorialPos Z     = (Z ** Refl)
factorialPos (S n) =
  case factorialPos n of
    (k ** prf) => ((k + n * S k) ** rewrite prf in Refl)

main : IO ()
main = putStrLn (show (factorial 5))

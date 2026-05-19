||| Length-indexed vectors and zipWith.
||| The type `Vec n A` carries the length as a type-level Nat, so the
||| zipWith function has no "lengths don't match" case to handle — the
||| type system has already eliminated that possibility.

module VecZipWith

%default total

data Vec : Nat -> Type -> Type where
  VNil  : Vec Z a
  VCons : a -> Vec n a -> Vec (S n) a

-- Both inputs and the output share the same length n.
-- The two-case pattern match is exhaustive precisely because Vec's
-- index rules out the (cons, nil) / (nil, cons) cases.
zipWith : (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f VNil          VNil          = VNil
zipWith f (VCons x xs) (VCons y ys)   = VCons (f x y) (zipWith f xs ys)

vecToList : Vec n a -> List a
vecToList VNil          = []
vecToList (VCons x xs) = x :: vecToList xs

xs : Vec 3 Nat
xs = VCons 1 (VCons 2 (VCons 3 VNil))

ys : Vec 3 Nat
ys = VCons 10 (VCons 20 (VCons 30 VNil))

main : IO ()
main = printLn (vecToList (VecZipWith.zipWith (+) xs ys))

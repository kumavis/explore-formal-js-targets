||| List reverse with proof that reverse is involutive: reverse (reverse xs) = xs.
||| Uses propositional equality (Refl) and rewrite tactics.

module Reverse

%default total

myReverse : List a -> List a
myReverse []        = []
myReverse (x :: xs) = myReverse xs ++ [x]

appendNilRight : (xs : List a) -> xs ++ [] = xs
appendNilRight []        = Refl
appendNilRight (x :: xs) = rewrite appendNilRight xs in Refl

appendAssoc : (xs, ys, zs : List a) -> (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendAssoc []        ys zs = Refl
appendAssoc (x :: xs) ys zs = rewrite appendAssoc xs ys zs in Refl

reverseAppend : (xs, ys : List a) -> myReverse (xs ++ ys) = myReverse ys ++ myReverse xs
reverseAppend []        ys = rewrite appendNilRight (myReverse ys) in Refl
reverseAppend (x :: xs) ys =
  rewrite reverseAppend xs ys in
  rewrite appendAssoc (myReverse ys) (myReverse xs) [x] in Refl

reverseReverse : (xs : List a) -> myReverse (myReverse xs) = xs
reverseReverse []        = Refl
reverseReverse (x :: xs) =
  rewrite reverseAppend (myReverse xs) [x] in
  rewrite reverseReverse xs in Refl

main : IO ()
main = printLn (myReverse (the (List Int) [1, 2, 3, 4]))

||| Insertion sort with a sortedness proof.
||| Sortedness is a *type-level* predicate; the proof is a constructive term
||| that Idris2's type checker verifies as well-formed.

module InsertionSort

import Data.Nat

%default total

-- A locally-defined transitivity on LTE that pattern matches enough to
-- bring the otherwise-erased indices into runtime scope.
lteTrans : {0 a, b, c : Nat} -> LTE a b -> LTE b c -> LTE a c
lteTrans LTEZero       _              = LTEZero
lteTrans (LTESucc ab) (LTESucc bc)    = LTESucc (lteTrans ab bc)

-- Decidable comparison built on Data.Nat.LTE.
data Order' : Nat -> Nat -> Type where
  Le : LTE x y -> Order' x y
  Gt : LTE y x -> Order' x y

compare' : (x, y : Nat) -> Order' x y
compare' Z     y     = Le LTEZero
compare' (S _) Z     = Gt LTEZero
compare' (S x) (S y) = case compare' x y of
                         Le p => Le (LTESucc p)
                         Gt p => Gt (LTESucc p)

-- "x is ≤ every element of xs".
data LowerBound : Nat -> List Nat -> Type where
  LB_Nil  : LowerBound x []
  LB_Cons : LTE x y -> LowerBound x ys -> LowerBound x (y :: ys)

-- Sortedness.
data Sorted : List Nat -> Type where
  S_Nil  : Sorted []
  S_Cons : LowerBound x xs -> Sorted xs -> Sorted (x :: xs)

-- If x ≤ y and y ≤* xs, then x ≤* xs.
lbTrans : {0 x, y : Nat} -> {0 xs : List Nat}
       -> LTE x y -> LowerBound y xs -> LowerBound x xs
lbTrans _   LB_Nil           = LB_Nil
lbTrans xy (LB_Cons yz rest) = LB_Cons (lteTrans xy yz) (lbTrans xy rest)

-- Value-level insertion.
insert : Nat -> List Nat -> List Nat
insert x []        = x :: []
insert x (y :: ys) = case compare' x y of
                       Le _ => x :: y :: ys
                       Gt _ => y :: insert x ys

-- Lemma: insert preserves "lo ≤ everything".
insertLB : {0 lo : Nat} -> (x : Nat) -> {xs : List Nat}
        -> LTE lo x -> LowerBound lo xs -> LowerBound lo (insert x xs)
insertLB x {xs = []}        loX LB_Nil          = LB_Cons loX LB_Nil
insertLB x {xs = (y :: ys)} loX (LB_Cons loY rest) with (compare' x y)
  insertLB x {xs = (y :: ys)} loX (LB_Cons loY rest) | Le _ = LB_Cons loX (LB_Cons loY rest)
  insertLB x {xs = (y :: ys)} loX (LB_Cons loY rest) | Gt _ = LB_Cons loY (insertLB x loX rest)

-- Theorem: insert preserves sortedness.
insertSorted : (x : Nat) -> (xs : List Nat) -> Sorted xs -> Sorted (insert x xs)
insertSorted x []        S_Nil           = S_Cons LB_Nil S_Nil
insertSorted x (y :: ys) (S_Cons lb syss) with (compare' x y)
  insertSorted x (y :: ys) (S_Cons lb syss) | Le xy = S_Cons (LB_Cons xy (lbTrans xy lb)) (S_Cons lb syss)
  insertSorted x (y :: ys) (S_Cons lb syss) | Gt yx = S_Cons (insertLB x yx lb) (insertSorted x ys syss)

-- The sort function.
sort : List Nat -> List Nat
sort []        = []
sort (x :: xs) = insert x (sort xs)

-- Theorem: sort always returns a sorted list.
sortSorted : (xs : List Nat) -> Sorted (sort xs)
sortSorted []        = S_Nil
sortSorted (x :: xs) = insertSorted x (sort xs) (sortSorted xs)

main : IO ()
main = printLn (sort [3, 1, 4, 1, 5, 9, 2, 6])

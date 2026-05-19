(* Coq has length-indexed vectors via Coq.Vectors.Vector, but extracting
   them through OCaml is brittle (the GADT-style encoding produces awkward
   Obj.magic dances). So this port follows the Dafny shape: zipWith on
   plain lists with a length-match runtime precondition.

   This is honest about Coq's position: it CAN express the length-indexed
   guarantee at the source level — see the comment block at the bottom —
   but the OCaml back end does not produce idiomatic JS from it. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Import ListNotations.

Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | x :: xs', y :: ys' => f x y :: zipWith f xs' ys'
  | _, _ => []
  end.

(* Verified property: if the inputs have the same length, the result has
   that length and each position holds the pointwise f of the inputs. *)
Lemma zipWith_length : forall A B C (f : A -> B -> C) xs ys,
  length xs = length ys -> length (zipWith f xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] Hlen; simpl; try discriminate.
  - reflexivity.
  - simpl in Hlen. injection Hlen as Hlen. rewrite (IH ys Hlen). reflexivity.
Qed.

(* If we'd wanted to forbid mismatched lengths *at the type level* the way
   Agda's Vec does, the source signature would be:

     Definition zipWithVec {A B C n} (f : A -> B -> C)
       (xs : Vector.t A n) (ys : Vector.t B n) : Vector.t C n :=
         Vector.map2 f xs ys.

   The proof obligation disappears (the type checker enforces n = n), but
   the extracted OCaml is not idiomatic and js_of_ocaml's output for
   Vector.t includes Obj.magic noise. The price of expressivity is paid
   at the seam. *)

Extraction Language OCaml.
Extraction "veczipwith.ml" zipWith.

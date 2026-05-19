(* List reverse with the involution proof, and extraction to OCaml. *)

Require Import Coq.Lists.List.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Import ListNotations.

Fixpoint myrev {A : Type} (xs : list A) : list A :=
  match xs with
  | []      => []
  | x :: xs' => myrev xs' ++ [x]
  end.

Lemma myrev_app : forall (A : Type) (xs ys : list A),
  myrev (xs ++ ys) = myrev ys ++ myrev xs.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Theorem myrev_involutive : forall (A : Type) (xs : list A),
  myrev (myrev xs) = xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite myrev_app. simpl. rewrite IH. reflexivity.
Qed.

Extraction Language OCaml.
Extraction "reverse.ml" myrev.

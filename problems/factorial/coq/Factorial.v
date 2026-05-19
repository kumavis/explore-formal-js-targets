(* Factorial in Coq, with extraction to OCaml. *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

Lemma fact_pos : forall n, 1 <= fact n.
Proof.
  induction n; simpl.
  - apply Nat.le_refl.
  - destruct (fact n) eqn:E.
    + inversion IHn.
    + apply le_n_S, Nat.le_0_l.
Qed.

Extraction Language OCaml.
Extraction "factorial.ml" fact.

(* Triangular-number closed form: 2 * Sum n = n * (n + 1).
   In Coq this is one induction plus `ring` (which handles the nonlinear
   arithmetic step Dafny's SMT solver does automatically). *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Fixpoint sum (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => S n' + sum n'
  end.

Theorem closed_form : forall n, 2 * sum n = n * (n + 1).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - (* Unfold sum once, substitute the IH, then let `nia` (nonlinear
       integer arithmetic) handle the algebra. *)
    change (sum (S n)) with (S n + sum n). nia.
Qed.

Extraction Language OCaml.
Extraction "sumformula.ml" sum.

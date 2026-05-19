(* Two capability patterns in Coq:

   1. CONSUMING — `validate` takes a host-supplied `nat -> bool` predicate
      and checks every element of a list. We *prove* an `iff` between
      the function's true-result and a propositional `Forall`, so callers
      get a real specification of what the boolean return value means.

   2. VENDING — Counter is declared as Coq `Parameter`s and bound to
      OCaml-side mutable-ref implementations via `Extract Constant`.
      The Coq side has nothing to prove about the bumps (it never sees
      the state), so this is purely an FFI seam — but the *type* of
      the interface is checked by Coq, and that's the contract OCaml/JS
      callers see. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Import ListNotations.

(* --- Direction 1: CONSUME a host predicate -------------------------------- *)

Fixpoint validate (check : nat -> bool) (xs : list nat) : bool :=
  match xs with
  | []      => true
  | x :: xs' => andb (check x) (validate check xs')
  end.

Theorem validate_iff_forall : forall check xs,
  validate check xs = true <-> Forall (fun x => check x = true) xs.
Proof.
  intros check xs. induction xs as [|x xs IH]; simpl; split; intros H.
  - apply Forall_nil.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [Hx Hxs].
    apply Forall_cons; [assumption | apply IH; assumption].
  - inversion H; subst.
    apply andb_true_iff. split; [assumption | apply IH; assumption].
Qed.

(* --- Direction 2: VEND a capability via Extract Constant ------------------ *)

Parameter Counter : Type.
Parameter new_counter : unit -> Counter.
Parameter bump : Counter -> nat.
Parameter read : Counter -> nat.

(* Bind the Coq parameters to the OCaml side. Coq has nothing to prove
   about these — bump/read live in OCaml's mutable world — but the
   *signatures* are now part of the verified interface and any consumer
   of the extracted module sees the typed shape. *)
Extract Constant Counter      => "int ref".
Extract Constant new_counter  => "(fun () -> ref 0)".
Extract Constant bump         => "(fun r -> incr r; !r)".
Extract Constant read         => "(fun r -> !r)".

Extraction Language OCaml.
Extraction "caps.ml" validate new_counter bump read.

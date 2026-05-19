(* Insertion sort over a list of nats, with a sortedness proof.
   We define our own Sorted / LowerBound predicates (mirroring the Agda
   and Idris2 versions) to make the proof structural and tractable. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Import ListNotations.

(* "lo is ≤ every element of xs". *)
Inductive LowerBound (lo : nat) : list nat -> Prop :=
  | lb_nil  : LowerBound lo []
  | lb_cons : forall x xs, lo <= x -> LowerBound lo xs -> LowerBound lo (x :: xs).

(* Sortedness as cons of (lower-bound, sortedness-of-tail). *)
Inductive Sorted : list nat -> Prop :=
  | s_nil  : Sorted []
  | s_cons : forall x xs, LowerBound x xs -> Sorted xs -> Sorted (x :: xs).

Fixpoint insert (x : nat) (xs : list nat) : list nat :=
  match xs with
  | []      => [x]
  | y :: ys =>
    if Nat.leb x y then x :: y :: ys else y :: insert x ys
  end.

Fixpoint sort (xs : list nat) : list nat :=
  match xs with
  | []      => []
  | x :: xs' => insert x (sort xs')
  end.

(* Convert `Nat.leb x y = false` to `y < x` without depending on
   `Nat.leb_nle` (post-8.9 lemma). *)
Lemma leb_false_lt : forall x y, Nat.leb x y = false -> y < x.
Proof.
  intros x y H. destruct (le_lt_dec x y) as [Hle | Hlt].
  - apply Nat.leb_le in Hle. rewrite Hle in H. discriminate.
  - assumption.
Qed.

(* If `lo <= x` and `lo` is below all of xs, then `lo` is below all of
   `insert x xs`. *)
Lemma insert_lower_bound : forall lo x xs,
  lo <= x -> LowerBound lo xs -> LowerBound lo (insert x xs).
Proof.
  intros lo x xs Hlx Hlb. induction Hlb as [|y ys Hloy Hlys IH]; simpl.
  - apply lb_cons; [assumption | apply lb_nil].
  - destruct (Nat.leb x y) eqn:Hxy.
    + apply lb_cons; [assumption|]. apply lb_cons; assumption.
    + apply lb_cons; assumption.
Qed.

(* Insert preserves sortedness. *)
Lemma insert_sorted : forall x xs, Sorted xs -> Sorted (insert x xs).
Proof.
  intros x xs Hs. induction Hs as [|y ys Hlb Hsy IH]; simpl.
  - apply s_cons; [apply lb_nil | apply s_nil].
  - destruct (Nat.leb x y) eqn:Hxy.
    + apply Nat.leb_le in Hxy.
      (* result is x :: y :: ys; need LowerBound x (y :: ys) and Sorted (y :: ys) *)
      apply s_cons.
      * apply lb_cons; [assumption|].
        (* Need LowerBound x ys. We have LowerBound y ys (Hlb) and x <= y. *)
        clear -Hxy Hlb. induction Hlb as [|z zs Hyz Hlzs IH']; constructor.
        -- apply Nat.le_trans with y; assumption.
        -- assumption.
      * apply s_cons; assumption.
    + apply leb_false_lt in Hxy.            (* Hxy : y < x *)
      assert (Hyx : y <= x) by (apply Nat.lt_le_incl; assumption).
      apply s_cons.
      * apply insert_lower_bound; assumption.
      * apply IH.
Qed.

(* Sort always produces a sorted list. *)
Theorem sort_sorts : forall xs, Sorted (sort xs).
Proof.
  induction xs as [|x xs IH]; simpl.
  - apply s_nil.
  - apply insert_sorted; assumption.
Qed.

Extraction Language OCaml.
Extraction "insertionsort.ml" sort.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition is_sorted_spec (lst : list nat) (res : bool) : Prop :=
  res = true <-> 
  (Sorted le lst /\ (forall x : nat, count_occ Nat.eq_dec lst x <= 2)).

Example test_case_1 : is_sorted_spec [5] true.
Proof.
  unfold is_sorted_spec.
  split.
  - intros _.
    split.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * constructor.
    + intros x.
      simpl.
      destruct (Nat.eq_dec 5 x).
      * apply le_S. apply le_n.
      * apply le_S. apply le_S. apply le_n.
  - intros _.
    reflexivity.
Qed.
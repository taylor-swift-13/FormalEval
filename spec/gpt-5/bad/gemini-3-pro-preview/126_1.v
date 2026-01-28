Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_sorted_spec (lst : list nat) (res : bool) : Prop :=
  res = true <-> Sorted le lst /\ (forall x : nat, le (count_occ Nat.eq_dec lst x) 2).

Example test_case : is_sorted_spec [5] true.
Proof.
  unfold is_sorted_spec.
  split.
  - intros _.
    split.
    + (* Prove Sorted le [5] *)
      apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + (* Prove count constraint *)
      intros x.
      simpl.
      destruct (Nat.eq_dec 5 x).
      * (* Case x = 5: count is 1. 1 <= 2 *)
        lia.
      * (* Case x <> 5: count is 0. 0 <= 2 *)
        lia.
  - intros _.
    reflexivity.
Qed.
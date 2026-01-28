Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition no_more_than_two_duplicates (lst : list nat) : Prop :=
  forall x : nat, count_occ Nat.eq_dec lst x <= 2.

Definition ascending_sorted (lst : list nat) : Prop :=
  Sorted Nat.le lst.

Definition is_sorted_spec (lst : list nat) (b : bool) : Prop :=
  b = true <-> (no_more_than_two_duplicates lst /\ ascending_sorted lst).

Example test_case_1 : is_sorted_spec [5] true.
Proof.
  unfold is_sorted_spec.
  split.
  - intros _.
    split.
    + (* Prove no_more_than_two_duplicates *)
      unfold no_more_than_two_duplicates.
      intros x.
      simpl.
      (* Destruct the equality decision to handle cases *)
      destruct (Nat.eq_dec 5 x) as [Heq | Hneq].
      * (* Case x = 5: count is 1. Goal: 1 <= 2 *)
        repeat constructor.
      * (* Case x <> 5: count is 0. Goal: 0 <= 2 *)
        repeat constructor.
    + (* Prove ascending_sorted *)
      unfold ascending_sorted.
      apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
  - intros _.
    reflexivity.
Qed.
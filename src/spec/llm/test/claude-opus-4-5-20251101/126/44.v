Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition count_occurrences (x : Z) (lst : list Z) : nat :=
  length (filter (Z.eqb x) lst).

Definition no_more_than_two_duplicates (lst : list Z) : Prop :=
  forall x : Z, (count_occurrences x lst <= 2)%nat.

Definition is_ascending (lst : list Z) : Prop :=
  forall i j : nat, (i < j)%nat -> (j < length lst)%nat ->
    match nth_error lst i, nth_error lst j with
    | Some a, Some b => a <= b
    | _, _ => True
    end.

Definition is_sorted_spec (lst : list Z) (result : bool) : Prop :=
  result = true <-> (is_ascending lst /\ no_more_than_two_duplicates lst).

Example test_unsorted_with_duplicates : is_sorted_spec [8%Z; 8%Z; 6%Z; 5%Z; 4%Z; 2%Z; 2%Z; 1%Z; 8%Z; 4%Z; 5%Z; 4%Z] false.
Proof.
  unfold is_sorted_spec.
  split.
  - intros H. discriminate.
  - intros [Hasc Hdup].
    exfalso.
    unfold is_ascending in Hasc.
    specialize (Hasc 0%nat 2%nat).
    simpl in Hasc.
    assert (H02: (0 < 2)%nat) by lia.
    assert (H2len: (2 < 12)%nat) by lia.
    specialize (Hasc H02 H2len).
    simpl in Hasc.
    lia.
Qed.
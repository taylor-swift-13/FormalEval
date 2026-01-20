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

Example test_not_sorted : is_sorted_spec [0%Z; 3%Z; 2%Z] false.
Proof.
  unfold is_sorted_spec.
  split.
  - intros H. discriminate.
  - intros [Hasc Hdup].
    exfalso.
    unfold is_ascending in Hasc.
    specialize (Hasc 1%nat 2%nat).
    assert (H1: (1 < 2)%nat) by lia.
    assert (H2: (2 < length [0%Z; 3%Z; 2%Z])%nat) by (simpl; lia).
    specialize (Hasc H1 H2).
    simpl in Hasc.
    lia.
Qed.
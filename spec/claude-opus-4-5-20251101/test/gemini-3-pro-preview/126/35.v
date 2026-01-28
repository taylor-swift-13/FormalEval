Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
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

Example test_case_2 : is_sorted_spec [1%Z; 2%Z; 3%Z; 6%Z; 4%Z; 5%Z; 6%Z; 7%Z; 4%Z; 8%Z; 8%Z] false.
Proof.
  unfold is_sorted_spec.
  split.
  - intros H. discriminate H.
  - intros [H_asc _].
    unfold is_ascending in H_asc.
    specialize (H_asc 3%nat 4%nat).
    simpl in H_asc.
    assert (H_lt : (3 < 4)%nat) by lia.
    assert (H_len : (4 < 11)%nat) by lia.
    specialize (H_asc H_lt H_len).
    lia.
Qed.
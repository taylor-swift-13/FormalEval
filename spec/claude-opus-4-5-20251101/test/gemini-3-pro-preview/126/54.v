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

Example test_case_1 : is_sorted_spec [8%Z; 8%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 6%Z] false.
Proof.
  unfold is_sorted_spec.
  split.
  - intros H. discriminate H.
  - intros [H_asc _].
    unfold is_ascending in H_asc.
    specialize (H_asc 1%nat 2%nat).
    assert (H_lt : (1 < 2)%nat) by lia.
    assert (H_len : (2 < length [8%Z; 8%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 6%Z])%nat).
    { simpl. lia. }
    specialize (H_asc H_lt H_len).
    simpl in H_asc.
    lia.
Qed.
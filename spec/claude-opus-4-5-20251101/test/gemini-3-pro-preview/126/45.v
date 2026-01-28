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

Example test_case_2 : is_sorted_spec [1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 4%Z] false.
Proof.
  unfold is_sorted_spec.
  split.
  - intros H. inversion H.
  - intros [H_asc H_dup].
    unfold no_more_than_two_duplicates in H_dup.
    specialize (H_dup 2%Z).
    unfold count_occurrences in H_dup.
    simpl in H_dup.
    lia.
Qed.
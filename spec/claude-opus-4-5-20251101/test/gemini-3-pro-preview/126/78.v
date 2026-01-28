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

Example test_case_2 : is_sorted_spec [0%Z; 3%Z] true.
Proof.
  unfold is_sorted_spec.
  split.
  - intros _.
    split.
    + unfold is_ascending.
      intros i j H_lt H_len.
      simpl in H_len.
      destruct i.
      * destruct j.
        -- lia.
        -- destruct j.
           ++ simpl. lia.
           ++ lia.
      * destruct j.
        -- lia.
        -- destruct j; lia.
    + unfold no_more_than_two_duplicates, count_occurrences.
      intros x.
      simpl.
      destruct (Z.eqb x 0); destruct (Z.eqb x 3); simpl; lia.
  - intros _.
    reflexivity.
Qed.
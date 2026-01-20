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

Example test_sorted_list : is_sorted_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z] true.
Proof.
  unfold is_sorted_spec.
  split.
  - intros _.
    split.
    + unfold is_ascending.
      intros i j Hij Hj.
      simpl in Hj.
      destruct i as [|i']; destruct j as [|j']; try lia.
      * simpl. destruct j' as [|j'']; simpl; try lia.
        destruct j'' as [|j''']; simpl; try lia.
        destruct j''' as [|j'''']; simpl; try lia.
        destruct j'''' as [|j''''']; simpl; try lia.
        destruct j''''' as [|j'''''']; simpl; try lia.
      * destruct i' as [|i'']; destruct j' as [|j'']; try (simpl; lia).
        destruct i'' as [|i''']; destruct j'' as [|j''']; try (simpl; lia).
        destruct i''' as [|i'''']; destruct j''' as [|j'''']; try (simpl; lia).
        destruct i'''' as [|i''''']; destruct j'''' as [|j''''']; try (simpl; lia).
        destruct i''''' as [|i'''''']; destruct j''''' as [|j'''''']; try (simpl; lia).
    + unfold no_more_than_two_duplicates.
      intros x.
      unfold count_occurrences.
      simpl.
      destruct (x =? 1)%Z eqn:H1; simpl;
      destruct (x =? 2)%Z eqn:H2; simpl;
      destruct (x =? 3)%Z eqn:H3; simpl;
      destruct (x =? 4)%Z eqn:H4; simpl;
      destruct (x =? 5)%Z eqn:H5; simpl;
      destruct (x =? 6)%Z eqn:H6; simpl; lia.
  - intros _. reflexivity.
Qed.
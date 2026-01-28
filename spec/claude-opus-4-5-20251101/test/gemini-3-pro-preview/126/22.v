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

Example test_case_1 : is_sorted_spec [1%Z; 2%Z; 2%Z; 3%Z; 4%Z; 4%Z; 5%Z] true.
Proof.
  unfold is_sorted_spec.
  split.
  - intros _.
    split.
    + unfold is_ascending.
      intros i j H_lt H_len.
      destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| simpl in H_len; lia ]]]]]]].
      all: destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| simpl in H_len; lia ]]]]]]].
      all: simpl; try lia.
    + unfold no_more_than_two_duplicates.
      intros x.
      unfold count_occurrences.
      simpl.
      destruct (Z.eqb x 1) eqn:E1. { apply Z.eqb_eq in E1. subst x. simpl. lia. }
      destruct (Z.eqb x 2) eqn:E2. { apply Z.eqb_eq in E2. subst x. simpl. lia. }
      destruct (Z.eqb x 3) eqn:E3. { apply Z.eqb_eq in E3. subst x. simpl. lia. }
      destruct (Z.eqb x 4) eqn:E4. { apply Z.eqb_eq in E4. subst x. simpl. lia. }
      destruct (Z.eqb x 5) eqn:E5. { apply Z.eqb_eq in E5. subst x. simpl. lia. }
      simpl. lia.
  - intros _. reflexivity.
Qed.
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

Example test_case_1 : is_sorted_spec [1%Z; 2%Z; 3%Z; 4%Z] true.
Proof.
  unfold is_sorted_spec.
  split.
  - intros _.
    split.
    + unfold is_ascending.
      intros i j H_lt H_len.
      simpl in H_len.
      destruct i.
      * destruct j; [lia|]. destruct j; [simpl; lia|]. destruct j; [simpl; lia|]. destruct j; [simpl; lia|]. lia.
      * destruct i.
        -- destruct j; [lia|]. destruct j; [lia|]. destruct j; [simpl; lia|]. destruct j; [simpl; lia|]. lia.
        -- destruct i.
           ++ destruct j; [lia|]. destruct j; [lia|]. destruct j; [lia|]. destruct j; [simpl; lia|]. lia.
           ++ lia.
    + unfold no_more_than_two_duplicates.
      intros x.
      unfold count_occurrences.
      simpl.
      destruct (Z.eqb x 1) eqn:H1; destruct (Z.eqb x 2) eqn:H2; 
      destruct (Z.eqb x 3) eqn:H3; destruct (Z.eqb x 4) eqn:H4; 
      simpl; try lia.
  - intros _.
    reflexivity.
Qed.
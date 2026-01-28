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

Example test_case_1 : is_sorted_spec [1%Z] true.
Proof.
  unfold is_sorted_spec.
  split.
  - (* Left to Right: result=true implies properties *)
    intros _.
    split.
    + (* Prove is_ascending *)
      unfold is_ascending.
      intros i j H_lt H_len.
      simpl in H_len.
      (* The list has length 1. j < 1 -> j = 0. i < j -> i < 0, impossible for nat. *)
      lia.
    + (* Prove no_more_than_two_duplicates *)
      unfold no_more_than_two_duplicates.
      intros x.
      unfold count_occurrences.
      simpl.
      (* Case analysis on whether x is equal to 1 *)
      destruct (Z.eqb x 1).
      * (* Case x == 1: count is 1 *)
        simpl. lia.
      * (* Case x != 1: count is 0 *)
        simpl. lia.
  - (* Right to Left: properties imply result=true *)
    intros _.
    reflexivity.
Qed.
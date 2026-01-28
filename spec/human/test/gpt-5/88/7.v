Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Definition problem_88_pre (input : list nat) : Prop := True.

Definition problem_88_spec (input output : list nat) : Prop :=
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: t =>
    let last_elem := last input h in
    if (h + last_elem) mod 2 =? 1 then
      Sorted le output
    else
      Sorted ge output
  end.

Example problem_88_test_empty : problem_88_spec [21; 14; 23; 11] [23; 21; 14; 11].
Proof.
  unfold problem_88_spec.
  split.
  - eapply Permutation_trans.
    + apply perm_skip. apply perm_swap.
    + apply perm_swap.
  - simpl.
    repeat constructor; try lia.
Qed.
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

Example problem_88_test_case : problem_88_spec [30; 20; 10; 5] [5; 10; 20; 30].
Proof.
  unfold problem_88_spec.
  split.
  - eapply Permutation_trans.
    + change [30; 20; 10; 5] with ([30; 20; 10] ++ [5]).
      change [5; 30; 20; 10] with ([5] ++ [30; 20; 10]).
      apply Permutation_app_comm.
    + apply Permutation_cons.
      eapply Permutation_trans.
      * change [30; 20; 10] with ([30; 20] ++ [10]).
        change [10; 30; 20] with ([10] ++ [30; 20]).
        apply Permutation_app_comm.
      * apply Permutation_cons.
        apply Permutation_swap.
  - simpl.
    repeat constructor; try lia.
Qed.
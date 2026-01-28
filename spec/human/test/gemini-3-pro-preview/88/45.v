Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
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

Example test_case_problem_88_1 : problem_88_spec [30; 20; 4; 5] [4; 5; 20; 30].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_trans with (l' := [20; 30; 4; 5]).
    + apply perm_swap.
    + apply Permutation_trans with (l' := [20; 4; 30; 5]).
      * apply perm_skip. apply perm_swap.
      * apply Permutation_trans with (l' := [4; 20; 30; 5]).
        -- apply perm_swap.
        -- apply Permutation_trans with (l' := [4; 20; 5; 30]).
           ++ apply perm_skip. apply perm_skip. apply perm_swap.
           ++ apply Permutation_trans with (l' := [4; 5; 20; 30]).
              ** apply perm_skip. apply perm_swap.
              ** apply Permutation_refl.
  - simpl.
    repeat constructor.
Qed.
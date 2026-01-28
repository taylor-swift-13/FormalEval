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
  | h :: _ =>
    let last_elem := last input h in
    if (h + last_elem) mod 2 =? 1 then
      Sorted le output
    else
      Sorted ge output
  end.

Example test_problem_88_descending : problem_88_spec [5; 7; 9; 11] [11; 9; 7; 5].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_trans with [5; 7; 9; 11].
    + apply Permutation_refl.
    + apply perm_trans with [7; 5; 9; 11].
      * apply perm_swap.
      * apply perm_trans with [7; 9; 5; 11].
        -- apply perm_skip. apply perm_swap.
        -- apply perm_trans with [7; 9; 11; 5].
           ++ apply perm_skip. apply perm_skip. apply perm_swap.
           ++ apply perm_trans with [9; 7; 11; 5].
              ** apply perm_swap.
              ** apply perm_trans with [9; 11; 7; 5].
                 --- apply perm_skip. apply perm_swap.
                 --- apply perm_trans with [11; 9; 7; 5].
                     +++ apply perm_swap.
                     +++ apply Permutation_refl.
  - simpl.
    repeat constructor.
Qed.
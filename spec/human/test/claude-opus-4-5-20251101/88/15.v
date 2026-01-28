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

Example test_problem_88_1_2_3 : problem_88_spec [1; 2; 3] [3; 2; 1].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_trans with (l' := [1; 2; 3]).
    + apply Permutation_refl.
    + apply perm_trans with (l' := [1; 3; 2]).
      * apply perm_skip. apply perm_swap.
      * apply perm_trans with (l' := [3; 1; 2]).
        -- apply perm_swap.
        -- apply perm_skip. apply perm_swap.
  - simpl.
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
      * apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
Qed.
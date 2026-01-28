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

Example test_problem_88_descending : problem_88_spec [7; 9; 11] [11; 9; 7].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_trans with [7; 11; 9].
    + apply perm_swap.
    + apply perm_trans with [11; 7; 9].
      * apply perm_swap.
      * apply perm_skip.
        apply perm_swap.
  - simpl.
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
      * apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
Qed.
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

Example test_problem_88_234 : problem_88_spec [2; 3; 4] [4; 3; 2].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_trans with (l' := [2; 3; 4]).
    + apply Permutation_refl.
    + apply perm_trans with (l' := [4; 2; 3]).
      * apply perm_trans with (l' := [2; 4; 3]).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * apply perm_skip. apply perm_swap.
  - simpl.
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
      * apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
Qed.
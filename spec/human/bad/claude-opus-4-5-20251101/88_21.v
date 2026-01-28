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

Example test_problem_88_979 : problem_88_spec [9; 7; 9] [9; 9; 7].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_trans with (l' := [9; 9; 7]).
    + apply Permutation_cons_app with (l1 := [9]) (l2 := [7]).
      simpl.
      apply perm_swap.
    + apply Permutation_refl.
  - simpl.
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + apply HdRel_cons.
      auto.
Qed.
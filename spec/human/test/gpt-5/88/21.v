Require Import List.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_88_pre (input : list Z) : Prop := True.

Definition problem_88_spec (input output : list Z) : Prop :=
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: t =>
    let last_elem := last input h in
    if Z.eqb (Z.modulo (h + last_elem) 2) 1 then
      Sorted Z.le output
    else
      Sorted Z.ge output
  end.

Example problem_88_test_nonempty : problem_88_spec [9%Z; 7%Z; 9%Z] [9%Z; 9%Z; 7%Z].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_skip. apply perm_swap.
  - simpl. repeat constructor; lia.
Qed.
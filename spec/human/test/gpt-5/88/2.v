Require Import List.
Require Import Coq.ZArith.ZArith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

Definition problem_88_pre (input : list Z) : Prop := True.

Definition problem_88_spec (input output : list Z) : Prop :=
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: t =>
    let last_elem := last input h in
    if Z.odd (h + last_elem) then
      Sorted Z.le output
    else
      Sorted Z.ge output
  end.

Example problem_88_test_singleton : problem_88_spec [5%Z] [5%Z].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_refl.
  - simpl. reflexivity.
Qed.
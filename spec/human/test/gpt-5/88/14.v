Require Import List.
Require Import ZArith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
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
    if Z.eqb ((h + last_elem) mod 2) 1 then
      Sorted Z.le output
    else
      Sorted Z.ge output
  end.

Example problem_88_test_increasing : problem_88_spec [0%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z] [0%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_refl.
  - simpl.
    replace (Z.eqb ((0%Z + 9%Z) mod 2%Z) 1%Z) with true by (vm_compute; reflexivity).
    repeat constructor; try lia.
Qed.
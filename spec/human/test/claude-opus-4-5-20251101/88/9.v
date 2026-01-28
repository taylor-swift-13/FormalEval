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

Example test_problem_88_1234 : problem_88_spec [1; 2; 3; 4] [1; 2; 3; 4].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_refl.
  - simpl.
    repeat constructor.
Qed.
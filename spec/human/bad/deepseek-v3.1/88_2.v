Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition problem_88_spec (input output : list (list nat)) : Prop :=
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: t =>
    let last_elem := last input (hd [0] h) in
    if (hd 0 h + last_elem) mod 2 =? 1 then
      Sorted (le) output
    else
      Sorted (ge) output
  end.

Example test_single_list : problem_88_spec [[5%Z]] [[5%Z]].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_refl.
  - reflexivity.
Qed.
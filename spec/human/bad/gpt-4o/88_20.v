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

Example sort_array_test_1 :
  problem_88_spec [7; 9; 9] [9; 9; 7].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_cons_app; apply Permutation_refl.
  - simpl. 
    assert (7 + 9 = 16) by reflexivity.
    rewrite H. simpl.
    assert (16 mod 2 = 0) by reflexivity.
    rewrite H0. simpl.
    apply Sorted_cons with (1 := le_n 9).
    apply Sorted_cons with (1 := le_n 9).
    apply Sorted_nil.
Qed.
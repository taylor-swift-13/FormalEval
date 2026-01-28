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

Example sort_array_test_2 :
  problem_88_spec [2; 4; 3; 0; 1; 5] [0; 1; 2; 3; 4; 5].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_sort. reflexivity.
  - unfold Sorted. apply Sorted_cons; auto.
    + apply Sorted_cons; auto.
      * apply Sorted_cons; auto.
        -- apply Sorted_cons; auto.
           ++ apply Sorted_cons; auto.
              ** apply Sorted_cons; auto.
                  --- apply Sorted_nil.
Qed.
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

Example problem_88_test_case : 
  problem_88_spec [2; 1] [1; 2].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_sym.
    apply Permutation_cons_app.
    apply Permutation_refl.
  - simpl.
    (* h = 2, last_elem = 1, (2+1) mod 2 = 1, so Sorted le output *)
    apply Sorted_inv.
    + apply le_n.
    + constructor.
      * apply le_S, le_n.
      * constructor.
  Qed.
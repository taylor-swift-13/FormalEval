Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition problem_88_pre (input : list nat) : Prop := True.

(* sort_array 函数的程序规约 *)
Definition problem_88_spec (input output : list nat) : Prop :=
  (* 输出必须是输入的排列 *)
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: t =>
    (* 安全地获取最后一个元素 *)
    let last_elem := last input h in
    if (h + last_elem) mod 2 =? 1 then
      Sorted le output
    else
      Sorted ge output
  end.

Example test_case_problem_88_example : problem_88_spec [10; 7; 9; 11; 11; 9] [7; 9; 9; 10; 11; 11].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_trans with (l' := [7; 10; 9; 11; 11; 9]).
    + constructor.
    + apply perm_skip.
      apply perm_trans with (l' := [9; 10; 11; 11; 9]).
      * constructor.
      * apply perm_skip.
        apply Permutation_sym.
        apply Permutation_cons_append.
  - simpl.
    repeat constructor.
Qed.
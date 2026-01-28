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

Example test_case_problem_88_1 : problem_88_spec [4; 2; 3; 1] [1; 2; 3; 4].
Proof.
  unfold problem_88_spec.
  split.
  - apply perm_trans with (1 :: 4 :: 2 :: 3 :: nil).
    + apply Permutation_sym. apply Permutation_cons_append.
    + apply perm_skip.
      apply perm_trans with (2 :: 4 :: 3 :: nil).
      * apply perm_swap.
      * apply perm_skip.
        apply perm_swap.
  - simpl.
    repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || apply HdRel_cons; auto).
Qed.
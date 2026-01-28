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

Example test_case_problem_88_custom : problem_88_spec [21; 14; 23; 11] [23; 21; 14; 11].
Proof.
  unfold problem_88_spec.
  split.
  - apply Permutation_sym.
    change [23; 21; 14; 11] with (23 :: [21; 14] ++ [11]).
    change [21; 14; 23; 11] with ([21; 14] ++ 23 :: [11]).
    apply Permutation_cons_app.
  - simpl.
    unfold ge.
    repeat constructor.
Qed.
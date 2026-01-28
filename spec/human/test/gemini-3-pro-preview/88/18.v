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
  | h :: _ =>
    (* 安全地获取最后一个元素 *)
    let last_elem := last input h in
    if (h + last_elem) mod 2 =? 1 then
      Sorted le output
    else
      Sorted ge output
  end.

Example test_case_problem_88_1 : problem_88_spec [0; 1; 11; 0; 0; 0] [11; 1; 0; 0; 0; 0].
Proof.
  unfold problem_88_spec.
  split.
  - (* Permutation proof *)
    (* Swap 1 and 11 inside the list *)
    assert (H1: Permutation [0; 1; 11; 0; 0; 0] (0 :: 11 :: 1 :: [0; 0; 0])).
    { apply perm_skip. apply perm_swap. }
    rewrite H1. clear H1.
    (* Swap 0 and 11 at the head *)
    assert (H2: Permutation (0 :: 11 :: 1 :: [0; 0; 0]) (11 :: 0 :: 1 :: [0; 0; 0])).
    { apply perm_swap. }
    rewrite H2. clear H2.
    (* Match head 11, then swap 0 and 1 *)
    apply perm_skip.
    apply perm_swap.
  - (* Logic proof *)
    simpl.
    unfold ge.
    repeat constructor.
Qed.
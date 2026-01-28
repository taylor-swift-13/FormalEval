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

Example test_case_problem_88_1 : problem_88_spec [15; 42; 87; 32; 11; 0] [0; 11; 15; 32; 42; 87].
Proof.
  unfold problem_88_spec.
  split.
  - change [15; 42; 87; 32; 11; 0] with ([15; 42; 87; 32; 11] ++ [0]).
    apply Permutation_trans with (l' := [0] ++ [15; 42; 87; 32; 11]).
    { apply Permutation_app_comm. }
    simpl. apply perm_skip.
    
    change [15; 42; 87; 32; 11] with ([15; 42; 87; 32] ++ [11]).
    apply Permutation_trans with (l' := [11] ++ [15; 42; 87; 32]).
    { apply Permutation_app_comm. }
    simpl. apply perm_skip.
    
    apply perm_skip.
    
    change [42; 87; 32] with ([42; 87] ++ [32]).
    apply Permutation_trans with (l' := [32] ++ [42; 87]).
    { apply Permutation_app_comm. }
    simpl. apply perm_skip.
    
    apply Permutation_refl.
  - simpl.
    repeat constructor.
Qed.
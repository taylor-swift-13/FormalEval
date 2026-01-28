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

Example test_case_problem_88_1 : problem_88_spec [10; 9; 7; 9; 7] [7; 7; 9; 9; 10].
Proof.
  unfold problem_88_spec.
  split.
  - (* Permutation proof *)
    apply Permutation_sym.
    
    (* Match first 7 *)
    change [10; 9; 7; 9; 7] with ([10; 9] ++ 7 :: [9; 7]).
    transitivity (7 :: ([10; 9] ++ [9; 7])).
    2: { apply Permutation_middle. }
    constructor.
    simpl.
    
    (* Match second 7 *)
    change [10; 9; 9; 7] with ([10; 9; 9] ++ 7 :: []).
    transitivity (7 :: ([10; 9; 9] ++ [])).
    2: { apply Permutation_middle. }
    constructor.
    simpl.
    
    (* Match first 9 *)
    change [10; 9; 9] with ([10] ++ 9 :: [9]).
    transitivity (9 :: ([10] ++ [9])).
    2: { apply Permutation_middle. }
    constructor.
    simpl.
    
    (* Match second 9 *)
    change [10; 9] with ([10] ++ 9 :: []).
    transitivity (9 :: ([10] ++ [])).
    2: { apply Permutation_middle. }
    constructor.
    simpl.
    
    (* Match 10 *)
    apply Permutation_refl.

  - (* Logic proof *)
    simpl.
    repeat constructor.
Qed.
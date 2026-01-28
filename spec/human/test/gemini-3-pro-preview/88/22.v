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

Example test_case_problem_88_custom : problem_88_spec [30; 2; 20; 10; 5] [2; 5; 10; 20; 30].
Proof.
  unfold problem_88_spec.
  split.
  - (* Permutation proof *)
    (* Goal: Permutation [30; 2; 20; 10; 5] [2; 5; 10; 20; 30] *)
    
    (* Step 1: Move 2 to the front *)
    assert (H1: Permutation [30; 2; 20; 10; 5] (2 :: [30; 20; 10; 5])).
    { apply perm_swap. }
    rewrite H1; clear H1.
    apply perm_skip.
    
    (* Step 2: Move 5 to the front of the remaining list *)
    (* Current LHS tail: [30; 20; 10; 5] *)
    change [30; 20; 10; 5] with ([30; 20; 10] ++ [5]).
    transitivity ([5] ++ [30; 20; 10]).
    { apply Permutation_app_comm. }
    simpl.
    apply perm_skip.
    
    (* Step 3: Move 10 to the front of the remaining list *)
    (* Current LHS tail: [30; 20; 10] *)
    change [30; 20; 10] with ([30; 20] ++ [10]).
    transitivity ([10] ++ [30; 20]).
    { apply Permutation_app_comm. }
    simpl.
    apply perm_skip.
    
    (* Step 4: Swap the remaining two elements [30; 20] to [20; 30] *)
    apply perm_swap.
    
  - (* Logic check *)
    simpl.
    (* Condition check: (30 + 5) mod 2 = 35 mod 2 = 1. *)
    (* Expect: Sorted le [2; 5; 10; 20; 30] *)
    repeat constructor.
    (* Solve inequalities like 2 <= 5, 5 <= 10, etc. *)
    all: repeat (apply le_n || apply le_S).
Qed.
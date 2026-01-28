Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(**
 * @spec problem_74_pre
 * @brief 程序前置条件：接受两个字符串列表作为输入。
 *)
Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

(**
 * @spec problem_74_spec
 * @brief 程序规约：选择两个字符串列表中总字符数较少的那个作为输出（若相等则选择第一个）。
 *)
Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example test_problem_74 : problem_74_spec [] [] [].
Proof.
  (* Unfold the specification definition *)
  unfold problem_74_spec.
  
  (* Simplify the expression. 
     fold_left on an empty list returns the accumulator (0).
     So, sum [] evaluates to 0. *)
  simpl.
  
  (* The goal becomes: (0 <= 0 /\ [] = []) \/ (0 > 0 /\ [] = []) *)
  (* Since 0 <= 0 is true, we prove the left side of the disjunction. *)
  left.
  
  (* Split the conjunction into two subgoals: 0 <= 0 and [] = [] *)
  split.
  - (* Subgoal 1: 0 <= 0 *)
    apply le_n.
  - (* Subgoal 2: [] = [] *)
    reflexivity.
Qed.
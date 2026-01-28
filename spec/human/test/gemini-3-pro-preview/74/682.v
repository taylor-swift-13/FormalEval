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

Example test_problem_74 : problem_74_spec ["qrstuv"; "wxyz"] ["qrstuv"; "wxyz"] ["qrstuv"; "wxyz"].
Proof.
  (* Unfold the specification definition *)
  unfold problem_74_spec.
  
  (* Simplify the expression. 
     Length of "qrstuv" is 6, length of "wxyz" is 4.
     Sum for both lists is 10. *)
  simpl.
  
  (* The goal becomes: (10 <= 10 /\ ["qrstuv"; "wxyz"] = ["qrstuv"; "wxyz"]) \/ ... *)
  (* Since 10 <= 10 is true, we prove the left side of the disjunction. *)
  left.
  
  (* Split the conjunction into two subgoals *)
  split.
  - (* Subgoal 1: 10 <= 10 *)
    apply le_n.
  - (* Subgoal 2: Equality of lists *)
    reflexivity.
Qed.
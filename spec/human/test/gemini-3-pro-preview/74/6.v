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

Example test_problem_74 : problem_74_spec ["hi"; "admin"] ["hI"; "hi"; "hi"] ["hI"; "hi"; "hi"].
Proof.
  (* Unfold the specification definition *)
  unfold problem_74_spec.
  
  (* Simplify the expression to calculate string lengths and sums.
     lst1 sum: 2 ("hi") + 5 ("admin") = 7.
     lst2 sum: 2 ("hI") + 2 ("hi") + 2 ("hi") = 6. *)
  simpl.
  
  (* The goal becomes: (7 <= 6 /\ ...) \/ (7 > 6 /\ ...) *)
  (* Since 7 > 6, we prove the right side of the disjunction. *)
  right.
  
  (* Split the conjunction into two subgoals: 7 > 6 and equality of lists *)
  split.
  - (* Subgoal 1: 7 > 6 *)
    repeat constructor.
  - (* Subgoal 2: ["hI"; "hi"; "hi"] = ["hI"; "hi"; "hi"] *)
    reflexivity.
Qed.
(* 引入必要的库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

(* 允许使用列表的标准表示法，例如 [a; b; c] *)
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

(* 证明测试用例 total_match([], []) ➞ [] *)

Example test_total_match_1 :
  problem_74_spec [] [] [].
Proof.
  unfold problem_74_spec.
  simpl.
  left.
  split.
  - reflexivity.
  - reflexivity.
Qed.
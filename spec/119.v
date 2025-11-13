(* You are given a list of two strings, both strings consist of open
parentheses '(' or close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if and only if all parentheses in S
are balanced. For example: the string '(())()' is good, while the string
'())' is not.
Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.

Examples:
match_parens(['()(', ')']) == 'Yes'
match_parens([')', ')']) == 'No' *)

(* 导入 Coq 的标准库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(*
  辅助函数 check_parens_inner
*)
Fixpoint check_parens_inner (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | "(" % char :: t => check_parens_inner t (S counter)
  | ")" % char :: t =>
    match counter with
    | 0 => false
    | S n' => check_parens_inner t n'
    end
  | _ :: t => check_parens_inner t counter
  end.

(*
  is_balanced 函数
*)
Definition is_balanced (l : list ascii) : bool :=
  check_parens_inner l 0.

(*
  先用命题刻画：是否存在一种拼接顺序得到“平衡”的字符串。
*)
Definition can_make_good (inputs : list (list ascii)) : Prop :=
  exists s1 s2,
    inputs = [s1; s2] /
    (is_balanced (s1 ++ s2) = true \/ is_balanced (s2 ++ s1) = true).

(*
  match_parens 的程序规约：
  - 如果可以通过某种拼接得到平衡串，则返回 "Yes"；
  - 否则返回 "No"；
  - 对于长度不是 2 的输入，也视为不可行，返回 "No"。
  说明：本规约为纯命题（Prop），不直接计算结果。
*)
Definition match_parens_spec (inputs : list (list ascii)) (result : string) : Prop :=
  (can_make_good inputs /\ result = "Yes"%string) \/
  (~ can_make_good inputs /\ result = "No"%string).
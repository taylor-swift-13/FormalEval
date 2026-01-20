(* Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> parse_nested_parens('(()()) ((())) () ((())()())')
[2, 3, 1, 3] *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.

(* 定义 '(' 和 ')' 和 ' ' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(*
  规约 1: MaxDepth(g)
  计算单个括号组的最大嵌套深度。
*)
Fixpoint max_depth_aux (g : list ascii) (current_depth max_seen : nat) : nat :=
  match g with
  | [] => max_seen
  | h :: t =>
    if ascii_dec h lparen then
      let new_depth := S current_depth in
      max_depth_aux t new_depth (Nat.max max_seen new_depth)
    else if ascii_dec h rparen then
      max_depth_aux t (Nat.pred current_depth) max_seen
    else
      max_depth_aux t current_depth max_seen (* 忽略其他字符 *)
  end.

Definition MaxDepth (g : list ascii) : nat :=
  max_depth_aux g 0 0.

(*
  规约 2: SplitOnSpaces(S)
  将一个字符列表按空格分割成一个列表的列表。
*)
Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : list ascii) : list (list ascii) :=
  match S with
  | [] =>
    match current_group with
    | [] => []
    | _ => [List.rev current_group]
    end
  | h :: t =>
    if ascii_dec h space then
      match current_group with
      | [] => SplitOnSpaces_aux [] t (* 多个或前导空格 *)
      | _ => (List.rev current_group) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : list ascii) : list (list ascii) :=
  SplitOnSpaces_aux [] S.

(*
  最终的程序规约: parse_nested_parens_spec(input, output)
  输入是 list ascii, 输出是 list nat。
*)

(*
  辅助断言: 检查一个字符是否为括号或空格
  直接使用等式，其类型为 Prop
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

Fixpoint IsBalanced_aux (l : list ascii) (count : nat) : Prop :=
  match l with
  | [] => count = 0
  | h :: t =>
    if ascii_dec h lparen then
      IsBalanced_aux t (S count)
    else if ascii_dec h rparen then
      match count with
      | 0 => False (* 右括号比左括号多，不平衡 *)
      | S n' => IsBalanced_aux t n'
      end
    else
      IsBalanced_aux t count (* 忽略其他字符 *)
  end.

Definition IsBalanced (l : list ascii) : Prop :=
  IsBalanced_aux l 0.
  
Fixpoint remove_spaces (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t =>
    if ascii_dec h space then
      remove_spaces t
    else
      h :: remove_spaces t
  end.
(*
  前提条件: separate_paren_groups_pre
  1. 输入列表中的所有字符都必须是括号或空格。
  2. 移除空格后的输入列表必须是平衡的。
  (这部分定义保持不变，因为它正确地使用了上面修正后的 is_paren_or_space)
*)
Definition separate_paren_groups_pre (input : list ascii) : Prop :=
  (Forall is_paren_or_space input) /\
  (IsBalanced (remove_spaces input)).
Definition parse_nested_parens_spec (input : list ascii) (output : list nat) : Prop :=
  output = List.map MaxDepth (SplitOnSpaces input).
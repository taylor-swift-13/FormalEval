(*Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
separate those group into separate strings and return the list of those.
Separate groups are balanced (each open brace is properly closed) and not nested within each other
Ignore any spaces in the input string.
>>> separate_paren_groups('( ) (( )) (( )( ))')
['()', '(())', '(()())'] *)

(* 引入所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.

(* 定义 '(' 和 ')' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(*
  规约 1: IsBalanced(l)
  使用一个辅助递归函数，其中 count 代表当前未闭合的左括号数。
*)
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

(*
  规约 2: IsMinimalBalanced(l)
  l 是平衡的，且不能被分解为两个更小的非空平衡列表。
*)
Definition IsMinimalBalanced (l : list ascii) : Prop :=
  IsBalanced l /\
  ~ (exists l1 l2,
       l1 <> [] /\
       l2 <> [] /\
       l = l1 ++ l2 /\
       IsBalanced l1 /\
       IsBalanced l2).

(*
  辅助函数: 移除列表中的空格
*)
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
  辅助断言: 检查一个字符是否为括号或空格
  直接使用等式，其类型为 Prop
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(*
  前提条件: separate_paren_groups_pre
  1. 输入列表中的所有字符都必须是括号或空格。
  2. 移除空格后的输入列表必须是平衡的。
  (这部分定义保持不变，因为它正确地使用了上面修正后的 is_paren_or_space)
*)
Definition separate_paren_groups_pre (input : list ascii) : Prop :=
  (Forall is_paren_or_space input) /\
  (IsBalanced (remove_spaces input)).
(*
  最终的程序规约: separate_paren_groups_spec(input, output)
  输入和输出都使用 list ascii。
*)
Definition separate_paren_groups_spec (input : list ascii) (output : list (list ascii)) : Prop :=
  (List.concat output = remove_spaces input) /\
  (Forall IsMinimalBalanced output).
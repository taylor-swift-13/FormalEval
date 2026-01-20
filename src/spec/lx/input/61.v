(*def correct_bracketing(brackets: str):
""" brackets is a string of "(" and ")".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("(")
False
>>> correct_bracketing("()")
True
>>> correct_bracketing("(()())")
True
>>> correct_bracketing(")(()")
False
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.

(*
 * 我们用一个归纳谓词来定义“一个括号列表是正确匹配的”。
 * 这个关系由三条规则构成：
 * 1. 基本情况 (cb_nil): 空列表是正确匹配的。
 * 2. 嵌套规则 (cb_nest): 如果 l 是正确匹配的，那么在 l 两侧加上 <> 后的新列表也是正确匹配的。
 * 3. 串联规则 (cb_concat): 如果 l1 和 l2 都是正确匹配的，那么将它们连接起来的列表也是正确的。
 *)
Inductive is_correctly_bracketed : list ascii -> Prop :=
  | cb_nil    : is_correctly_bracketed []
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("("%char :: l ++ [")"%char])
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

(*
 * correct_bracketing 函数的程序规约
 *
 * 描述了输入列表 brackets (list ascii) 与输出布尔值 b 之间的关系。
 *)
Definition correct_bracketing_spec (brackets : list ascii) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.
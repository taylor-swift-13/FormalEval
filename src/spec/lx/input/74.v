(* def total_match(lst1, lst2):
'''
Write a function that accepts two lists of strings and returns the list that has
total number of chars in the all strings of the list less than the other list.

if the two lists have the same number of chars, return the first list.

Examples
total_match([], []) ➞ []
total_match(['hi', 'admin'], ['hI', 'Hi']) ➞ ['hI', 'Hi']
total_match(['hi', 'admin'], ['hi', 'hi', 'admin', 'project']) ➞ ['hi', 'admin']
total_match(['hi', 'admin'], ['hI', 'hi', 'hi']) ➞ ['hI', 'hi', 'hi']
total_match(['4'], ['1', '2', '3', '4', '5']) ➞ ['4']
'''*)
(* 引入必要的库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

(* 允许使用列表的标准表示法，例如 [a; b; c] *)
Import ListNotations.

(**
 * @function total_chars
 * @brief 计算一个字符串列表中所有字符的总数。
 * @param l: 一个字符串列表 (list string)。
 * @return: 列表中所有字符串长度之和 (nat)。
 *)
Fixpoint total_chars (l : list string) : nat :=
  match l with
  | [] => 0
  | h :: t => String.length h + total_chars t
  end.

(**
 * @spec total_match_spec
 * @brief total_match 函数的程序规约。
 * 该规约描述了输入列表 lst1, lst2 与输出列表 output 之间的关系。
 *
 * @param lst1: 第一个输入字符串列表。
 * @param lst2: 第二个输入字符串列表。
 * @param output: 函数的输出字符串列表。
 * @prop:
 *   如果 lst1 的总字符数小于或等于 lst2，则输出必须是 lst1。
 *   否则（即 lst1 的总字符数大于 lst2），输出必须是 lst2。
 *)
Definition total_match_spec (lst1 lst2 output : list string) : Prop :=
  (total_chars lst1 <= total_chars lst2 /\ output = lst1) \/
  (total_chars lst1 > total_chars lst2 /\ output = lst2).
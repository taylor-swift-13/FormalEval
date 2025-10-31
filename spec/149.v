(* def sorted_list_sum(lst):
"""Write a function that accepts a list of strings as a parameter,
deletes the strings that have odd lengths from it,
and returns the resulted list with a sorted order,
The list is always a list of strings and never an array of numbers,
and it may contain duplicates.
The order of the list should be ascending by length of each word, and you
should return the list sorted by that rule.
If two words have the same length, sort the list alphabetically.
The function should return a list of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert list_sort(["aa", "a", "aaa"]) => ["aa"]
assert list_sort(["ab", "a", "aaa", "cd"]) => ["ab", "cd"]
""" *)
(* 引入必要的 Coq 标准库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Permutation.
Import ListNotations.

(*
  Coq 中没有内置的 string 类型，我们根据要求使用 `list ascii` 来表示字符串。
  例如，字符串 "ab" 表示为 ('a'%char :: 'b'%char :: nil)。
*)

(* 辅助定义 1: 字典序比较 `lex_le` *)
(* s1 <= s2 当且仅当 s1 在字典序上小于等于 s2。*)
Fixpoint lex_le (s1 s2 : list ascii) : Prop :=
  match s1, s2 with
  | [], _ => True
  | _::_, [] => False
  | c1::s1', c2::s2' =>
    match Ascii.compare c1 c2 with
    | Lt => True
    | Gt => False
    | Eq => lex_le s1' s2'
    end
  end.

(* 辅助定义 2: 字符串（list ascii）的完整比较关系 `string_le` *)
(* s1 <= s2 当且仅当:
   - length s1 < length s2, 或者
   - length s1 = length s2 且 s1 按字典序小于等于 s2.
*)
Definition string_le (s1 s2 : list ascii) : Prop :=
  match Nat.compare (length s1) (length s2) with
  | Lt => True
  | Gt => False
  | Eq => lex_le s1 s2
  end.

(* 辅助定义 3: 判断列表是否已排序的属性 `Sorted` *)
Inductive Sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : Sorted R []
| sorted_one : forall x, Sorted R [x]
| sorted_cons : forall x y l, R x y -> Sorted R (y :: l) -> Sorted R (x :: y :: l).

(* 辅助定义 4: 判断字符串长度是否为偶数的属性 *)
Definition has_even_length (s : list ascii) : bool :=
  Nat.even (length s).

(*
  程序规约 Spec
  它定义了输入列表 `lst_in` 和输出列表 `lst_out` 之间的关系。
*)
Definition Spec (lst_in lst_out : list (list ascii)) : Prop :=
  (* 关系 1: `lst_out` 是对 `lst_in` 中所有偶数长度字符串进行过滤后得到的结果的一个排列。*)
  Permutation lst_out (filter has_even_length lst_in) /\

  (* 关系 2: `lst_out` 必须是根据 `string_le` 规则排序好的。*)
  Sorted string_le lst_out.
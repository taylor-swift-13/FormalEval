(* def solve(s):
"""You are given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
solve("1234") = "4321"
solve("ab") = "AB"
solve("#a@C") = "#A@c"
""" *)
(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith. (* 需要引入这个库来进行自然数运算 *)
Import ListNotations.

(*
  辅助定义
*)

(* 判断一个 ascii 字符是否为小写字母 *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

(* 判断一个 ascii 字符是否为大写字母 *)
Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

(* 判断一个 ascii 字符是否为字母 *)
Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

(* 自定义的大小写转换函数 *)

(* 将小写字母转为大写。如果不是小写字母，则保持不变。
   原理：nat_of_ascii a - 32 *)
Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

(* 将大写字母转为小写。如果不是大写字母，则保持不变。
   原理：nat_of_ascii a + 32 *)
Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* 定义一个函数 change_case 来转换字母的大小写。
   现在它使用我们自定义的转换函数。 *)
Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

(* 定义一个递归函数 contains_letter_dec 来判断一个列表 (字符串) 是否包含任何字母。*)
Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || contains_letter_dec t
  end.

(*
  程序规约 (Program Specification)
*)

(* solve_spec 是一个规约，它描述了输入列表 s 和输出列表 s' 之间的关系。
   - 如果 s 包含至少一个字母 (contains_letter_dec s = true),
     那么输出 s' 必须是 s 中每个字符应用 change_case 函数后的结果。
   - 否则 (s 不包含任何字母),
     输出 s' 必须是 s 的反转。
*)
Definition solve_spec (s s' : list ascii) : Prop :=
  if contains_letter_dec s
  then s' = map change_case s
  else s' = rev s.
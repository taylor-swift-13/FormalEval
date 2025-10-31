(* def digitSum(s):
Task
Write a function that takes a string as input and returns the sum of the upper characters only'
ASCII codes.

Examples:
digitSum("") => 0
digitSum("abAB") => 131
digitSum("abcCd") => 67
digitSum("helloE") => 69
digitSum("woArBld") => 131
digitSum("aAaaaXa") => 153 *)

Require Import Coq.Strings.Ascii Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(*
  * @brief 检查一个ASCII字符是否为大写字母。
  * @param c 要检查的字符。
  * @return 如果c是大写字母(A-Z)，则返回true，否则返回false。
*)
Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 65 n) && (Nat.leb n 90).

(*
  * @brief 递归计算一个ASCII字符列表中所有大写字母的ASCII码之和。
  * @param l ASCII字符列表。
  * @return 列表中所有大写字母ASCII码的总和。
*)
Fixpoint sum_uppercase_ascii (l : list ascii) : nat :=
  match l with
  | [] => 0
  | c :: t =>
    if is_uppercase c
    then nat_of_ascii c + sum_uppercase_ascii t
    else sum_uppercase_ascii t
  end.

(*
  * @brief digitSum程序的规约 (Specification)。
  * 它描述了输入字符列表 l 与输出自然数 n 之间的关系。
  * @param l 输入的ASCII字符列表。
  * @param n 输出的自然数。
  * @return 一个Prop，当 n 等于 l 中所有大写字母的ASCII码之和时为真。
*)
Definition digitSum_spec (l : list ascii) (n : nat) : Prop :=
  n = sum_uppercase_ascii l.
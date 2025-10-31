(* def vowels_count(s):
"""Write a function vowels_count which takes a string representing
a word as input and returns the number of vowels in the string.
Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
vowel, but only when it is at the end of the given word.

Example:
>>> vowels_count("abcde")
2
>>> vowels_count("ACEDY")
3
""" *)
(* 导入 Coq 标准库中关于字符串、ASCII 字符、自然数和布尔值的定义 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

(* 打开字符串和布尔值的作用域，以方便使用相关操作符 *)
Open Scope string_scope.
Open Scope bool_scope.

(*
  定义一个辅助函数 `is_vowel_char`，用于判断一个 ASCII 字符是否是元音 'a', 'e', 'i', 'o', 'u'（忽略大小写）。
*)
Definition is_vowel_char (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(*
  定义一个辅助函数 `is_y`，用于判断一个 ASCII 字符是否是 'y'（忽略大小写）。
*)
Definition is_y (c : ascii) : bool :=
  match c with
  | "y"%char | "Y"%char => true
  | _ => false
  end.

(*
  定义一个递归函数 `vowels_count_func`，它精确地实现了计算元音数量的逻辑。
  - 如果字符串为空，元音数量为 0。
  - 否则，它检查第一个字符：
    - 如果是 'a', 'e', 'i', 'o', 'u' 之一，则计数加 1，然后递归计算剩余字符串。
    - 如果是 'y' 并且它位于字符串的末尾（即剩余字符串为空），则计数加 1，然后递归计算剩余字符串。
    - 其他情况下，直接递归计算剩余字符串。
*)
Fixpoint vowels_count_func (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
    let rest_count := vowels_count_func s' in
    if is_vowel_char c then
      1 + rest_count
    else if (is_y c) && (s' =? EmptyString) then
      1 + rest_count
    else
      rest_count
  end.

(*
  这是 `vowels_count` 函数的程序规约 (Specification)。
  它是一个一阶逻辑命题，表达了输入字符串 `s` 和输出自然数 `count` 之间的关系。
  这个规约声明，任何一个满足此规约的 `vowels_count` 函数的返回值 `count`，
  都必须等于 `vowels_count_func` 对输入字符串 `s` 的计算结果。
*)
Definition vowels_count_spec (s : string) (count : nat) : Prop :=
  count = vowels_count_func s.
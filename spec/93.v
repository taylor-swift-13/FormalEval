(*def encode(message):
"""
Write a function that takes a message, and encodes in such a
way that it swaps case of all letters, replaces all vowels in
the message with the letter that appears 2 places ahead of that
vowel in the english alphabet.
Assume only letters.

Examples:
>>> encode('test')
'TGST'
>>> encode('This is a message')
'tHKS KS C MGSSCGG'
""" *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope. (* 打开作用域以使用 "%char" 表示法 *)

(* 辅助函数：检查一个字符是否是元音 *)
Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(* 辅助函数：转换字母的大小写 *)
(* 此为规约目的的简化版本 *)
Definition swap_case (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (leb 65 n) (leb n 90) (* 是大写字母吗？ *)
  then ascii_of_nat (n + 32) (* 转换为小写 *)
  else if andb (leb 97 n) (leb n 122) (* 是小写字母吗？ *)
  then ascii_of_nat (n - 32) (* 转换为大写 *)
  else c. (* 不是字母，保持原样 *)

(* 辅助函数：将元音替换为两个位置之后的字母 *)
Definition replace_vowel (c : ascii) : ascii :=
  match c with
  | "a"%char => "c"%char | "e"%char => "g"%char | "i"%char => "k"%char | "o"%char => "q"%char | "u"%char => "w"%char
  | "A"%char => "C"%char | "E"%char => "G"%char | "I"%char => "K"%char | "O"%char => "Q"%char | "U"%char => "W"%char
  | _ => c
  end.

(* 单个字符编码的规约 *)
Inductive encode_char_spec (c_in c_out : ascii) : Prop :=
| mk_encode_char_spec :
    let c_swapped := swap_case c_in in
    (if is_vowel c_in
     then c_out = replace_vowel c_swapped
     else c_out = c_swapped) ->
    encode_char_spec c_in c_out.

(* 完整 encode 函数的规约 *)
Definition encode_spec (l_in l_out : list ascii) : Prop :=
 Forall2 encode_char_spec l_in l_out.
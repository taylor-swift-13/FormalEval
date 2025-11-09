(* def words_in_sentence(sentence):
"""
You are given a string representing a sentence,
the sentence contains some words separated by a space,
and you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
Input: sentence = "This is a test"
Output: "is"

Example 2:
Input: sentence = "lets go for swimming"
Output: "go for"

Constraints:
* 1 <= len(sentence) <= 100
* sentence contains only letters
""" *)
(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(*
  has_divisor_from n d 检查 n 是否有
  一个从 d 到 2 的除数。这是一个可计算的布尔函数。
*)
Fixpoint has_divisor_from (n d : nat) : bool :=
  match d with
  | 0 => false
  | 1 => false
  | S d' => (* 这里 d = d' + 1 *)
      if (n mod d =? 0)%nat
      then true
      (* 递归调用作用于 d'，它在结构上小于 d = S d' *)
      else has_divisor_from n d'
  end.

(*
  is_prime_bool n 判断 n 是否为素数，返回一个布尔值。
  1. n <= 1 不是素数。
  2. n > 1 时，当且仅当它没有任何从 n-1 到 2 的除数时，它才是素数。
*)
Definition is_prime_bool (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _ => negb (has_divisor_from n (n - 1)) (* negb 是布尔否定 *)
  end.

(*
  join_words ws 将一个单词列表（list (list ascii)）用空格连接成一个句子（list ascii）。
*)
Fixpoint join_words (words : list (list ascii)) : list ascii :=
  match words with
  | [] => []
  | w :: nil => w
  | w :: rest => w ++ (" "%char :: nil) ++ join_words rest
  end.

(*
  程序规约：words_in_sentence_spec
  它描述了输入 sentence 和输出 result 之间的关系。
*)
Definition words_in_sentence_spec (sentence : list ascii) (result : list ascii) : Prop :=
  exists (words : list (list ascii)),
    sentence = join_words words /\
    result = join_words (List.filter (fun w => is_prime_bool (length w)) words).
(* def anti_shuffle(s):
"""
Write a function that takes a string and returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words and blank spaces in the sentence.

For example:
anti_shuffle('Hi') returns 'Hi'
anti_shuffle('hello') returns 'ehllo'
anti_shuffle('Hello World!!!') returns 'Hello !!!Wdlor'
""" *)
(* 引入 Coq 标准库中关于字符串、列表、算术和置换的理论 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.

Import ListNotations.

(*
 * 辅助定义 1：is_space
 * 一个断言，当且仅当字符 c 是空格时为真。
 *)
Definition is_space (c : ascii) : Prop := c = " "%char.

(*
 * 辅助定义 2：is_sorted
 * 一个断言，当且仅当一个字符列表中的所有字符都根据其 ASCII 值按升序排列时为真。
 *)
Fixpoint is_sorted (s : list ascii) : Prop :=
  match s with
  | [] => True
  | c1 :: tl =>
      match tl with
      | [] => True
      | c2 :: _ => (nat_of_ascii c1 <= nat_of_ascii c2) /\ is_sorted tl
      end
  end.

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Fixpoint insert_char (c : ascii) (l : list ascii) : list ascii :=
  match l with
  | [] => [c]
  | h :: t =>
      if Nat.leb (nat_of_ascii c) (nat_of_ascii h) then
        c :: l
      else
        h :: insert_char c t
  end.

Fixpoint sort_chars (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t => insert_char h (sort_chars t)
  end.

Fixpoint process_word (l : list ascii) : list ascii :=
  sort_chars l.

Fixpoint split_words (l : list ascii) (current_word : list ascii) : list (list ascii) :=
  match l with
  | [] =>
      match current_word with
      | [] => []
      | _ => [current_word]
      end
  | h :: t =>
      if is_space_bool h then
        match current_word with
        | [] => split_words t []
        | _ => current_word :: split_words t []
        end
      else
        split_words t (current_word ++ [h])
  end.

Fixpoint merge_words (words : list (list ascii)) (spaces : list ascii) : list ascii :=
  match words, spaces with
  | [], _ => []
  | [w], [] => process_word w
  | w :: rest_words, s :: rest_spaces =>
      process_word w ++ [s] ++ merge_words rest_words rest_spaces
  | _, _ => []
  end.

Fixpoint extract_spaces (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t =>
      if is_space_bool h then
        h :: extract_spaces t
      else
        extract_spaces t
  end.

Definition anti_shuffle_impl (s : list ascii) : list ascii :=
  let words := split_words s [] in
  let spaces := extract_spaces s in
  merge_words words spaces.

Definition anti_shuffle_spec (s s_out : list ascii) : Prop :=
  s_out = anti_shuffle_impl s.
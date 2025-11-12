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

Definition is_space (c : ascii) : Prop := c = " "%char.

Inductive is_sorted_rel : list ascii -> Prop :=
  | isr_nil : is_sorted_rel []
  | isr_single : forall c, is_sorted_rel [c]
  | isr_cons : forall c1 c2 tl,
      (nat_of_ascii c1 <= nat_of_ascii c2) ->
      is_sorted_rel (c2 :: tl) ->
      is_sorted_rel (c1 :: c2 :: tl).

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Inductive insert_char_rel : ascii -> list ascii -> list ascii -> Prop :=
  | icr_nil : forall c, insert_char_rel c [] [c]
  | icr_insert : forall c h t,
      (nat_of_ascii c <= nat_of_ascii h) ->
      insert_char_rel c (h :: t) (c :: h :: t)
  | icr_skip : forall c h t result,
      (nat_of_ascii c > nat_of_ascii h) ->
      insert_char_rel c t result ->
      insert_char_rel c (h :: t) (h :: result).

Inductive sort_chars_rel : list ascii -> list ascii -> Prop :=
  | scr_nil : sort_chars_rel [] []
  | scr_cons : forall h t sorted_tail result,
      sort_chars_rel t sorted_tail ->
      insert_char_rel h sorted_tail result ->
      sort_chars_rel (h :: t) result.

Inductive process_word_rel : list ascii -> list ascii -> Prop :=
  | pwr_base : forall l sorted, sort_chars_rel l sorted -> process_word_rel l sorted.

(* 精确保留空白：以流式关系在遇到空格时冲刷当前词（排序后输出），空格原样输出。 *)
Inductive anti_shuffle_aux_rel : list ascii -> list ascii (* current word rev *) -> list ascii (* out *) -> Prop :=
  | asar_nil_empty : anti_shuffle_aux_rel [] [] []
  | asar_nil_nonempty : forall cur_rev sorted,
      sort_chars_rel cur_rev sorted ->
      anti_shuffle_aux_rel [] cur_rev sorted
  | asar_space : forall h t cur_rev sorted out_tail out,
      is_space_bool h = true ->
      sort_chars_rel cur_rev sorted ->
      anti_shuffle_aux_rel t [] out_tail ->
      out = sorted ++ [h] ++ out_tail ->
      anti_shuffle_aux_rel (h :: t) cur_rev out
  | asar_char : forall h t cur_rev out,
      is_space_bool h = false ->
      anti_shuffle_aux_rel t (h :: cur_rev) out ->
      anti_shuffle_aux_rel (h :: t) cur_rev out.

Definition anti_shuffle_spec (s s_out : list ascii) : Prop :=
  anti_shuffle_aux_rel s [] s_out.

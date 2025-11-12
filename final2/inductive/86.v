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

Inductive split_words_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
  | swr_nil_empty : forall current_word, current_word = [] -> split_words_rel current_word [] []
  | swr_nil_nonempty : forall current_word, current_word <> [] -> split_words_rel current_word [] [current_word]
  | swr_space_empty : forall current_word h t result,
      is_space_bool h = true ->
      current_word = [] ->
      split_words_rel [] t result ->
      split_words_rel current_word (h :: t) result
  | swr_space_nonempty : forall current_word h t result,
      is_space_bool h = true ->
      current_word <> [] ->
      split_words_rel [] t result ->
      split_words_rel current_word (h :: t) (current_word :: result)
  | swr_char : forall current_word h t result,
      is_space_bool h = false ->
      split_words_rel (current_word ++ [h]) t result ->
      split_words_rel current_word (h :: t) result.

Inductive merge_words_rel : list (list ascii) -> list ascii -> list ascii -> Prop :=
  | mwr_nil : forall spaces, merge_words_rel [] spaces []
  | mwr_single : forall w spaces processed,
      process_word_rel w processed ->
      spaces = [] ->
      merge_words_rel [w] spaces processed
  | mwr_cons : forall w rest_words s rest_spaces processed_w result_rest result,
      process_word_rel w processed_w ->
      merge_words_rel rest_words rest_spaces result_rest ->
      result = processed_w ++ [s] ++ result_rest ->
      merge_words_rel (w :: rest_words) (s :: rest_spaces) result.

Inductive extract_spaces_rel : list ascii -> list ascii -> Prop :=
  | esr_nil : extract_spaces_rel [] []
  | esr_space : forall h t result,
      is_space_bool h = true ->
      extract_spaces_rel t result ->
      extract_spaces_rel (h :: t) (h :: result)
  | esr_char : forall h t result,
      is_space_bool h = false ->
      extract_spaces_rel t result ->
      extract_spaces_rel (h :: t) result.

Definition anti_shuffle_spec (s s_out : list ascii) : Prop :=
  exists words spaces,
    split_words_rel [] s words /\
    extract_spaces_rel s spaces /\
    merge_words_rel words spaces s_out.

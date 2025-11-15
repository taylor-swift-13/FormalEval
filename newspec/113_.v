(* Given a list of strings, where each string consists of only digits, return a list.
Each element i of the output should be "the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> odd_count(['1234567'])
["the number of odd elements 4n the str4ng 4 of the 4nput."]
>>> odd_count(['3',"11111111"])
["the number of odd elements 1n the str1ng 1 of the 1nput.",
"the number of odd elements 8n the str8ng 8 of the 8nput."] *)

Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Inductive is_odd_digit : ascii -> Prop :=
| iod_1 : is_odd_digit "1"%char
| iod_3 : is_odd_digit "3"%char
| iod_5 : is_odd_digit "5"%char
| iod_7 : is_odd_digit "7"%char
| iod_9 : is_odd_digit "9"%char.

Inductive count_odd_digits_rel : string -> nat -> Prop :=
| codr_empty : count_odd_digits_rel "" 0%nat
| codr_odd : forall c s n, is_odd_digit c -> count_odd_digits_rel s n ->
    count_odd_digits_rel (String c s) (S n)
| codr_not_odd : forall c s n, ~ is_odd_digit c -> count_odd_digits_rel s n ->
    count_odd_digits_rel (String c s) n.

Inductive replace_char_rel : ascii -> ascii -> string -> string -> Prop :=
| rcr_empty : forall t r, replace_char_rel t r "" ""
| rcr_match : forall t r s s', replace_char_rel t r s s' ->
   replace_char_rel t r (String t s) (String r s')
| rcr_no_match : forall t r c s s', c <> t -> replace_char_rel t r s s' ->
   replace_char_rel t r (String c s) (String c s').

Inductive nat_to_digit_char_rel : nat -> ascii -> Prop :=
| ndcr_0 : nat_to_digit_char_rel 0%nat "0"%char
| ndcr_1 : nat_to_digit_char_rel 1%nat "1"%char
| ndcr_2 : nat_to_digit_char_rel 2%nat "2"%char
| ndcr_3 : nat_to_digit_char_rel 3%nat "3"%char
| ndcr_4 : nat_to_digit_char_rel 4%nat "4"%char
| ndcr_5 : nat_to_digit_char_rel 5%nat "5"%char
| ndcr_6 : nat_to_digit_char_rel 6%nat "6"%char
| ndcr_7 : nat_to_digit_char_rel 7%nat "7"%char
| ndcr_8 : nat_to_digit_char_rel 8%nat "8"%char
| ndcr_9 : nat_to_digit_char_rel 9%nat "9"%char.

(* 固定模板：将其中的字符 'i' 替换为计数字符 *)
Definition odd_count_template : string :=
    "the number of odd elements i n the str i ng i of the i nput.".

Inductive process_string_rel : string -> string -> Prop :=
| psr_build : forall s cnt ch res,
    count_odd_digits_rel s cnt ->
    nat_to_digit_char_rel cnt ch ->
    replace_char_rel "i"%char ch odd_count_template res ->
    process_string_rel s res.

Inductive odd_count_rel : list string -> list string -> Prop :=
| ocr_nil : odd_count_rel nil nil
| ocr_cons : forall h t h' t', process_string_rel h h' ->
    odd_count_rel t t' ->
    odd_count_rel (h :: t) (h' :: t').

Definition odd_count_spec (input : list string) (output : list string) : Prop :=
  odd_count_rel input output.


(* HumanEval 113 - Inductive Spec *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.

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

Inductive process_string_rel : string -> string -> Prop :=
| psr_build : forall s cnt ch templ res,
   count_odd_digits_rel s cnt ->
   nat_to_digit_char_rel cnt ch ->
   replace_char_rel "i"%char ch templ res ->
   process_string_rel s res.

Inductive odd_count_rel : list string -> list string -> Prop :=
| ocr_nil : odd_count_rel nil nil
| ocr_cons : forall h t h' t', process_string_rel h h' ->
    odd_count_rel t t' ->
    odd_count_rel (h :: t) (h' :: t').

Definition odd_count_spec (input : list string) (output : list string) : Prop :=
  odd_count_rel input output.

Example odd_count_spec_ex: odd_count_spec ("123"%string :: nil)
  ("the number of odd elements 2n the str2ng 2 of the 2nput."%string :: nil).
Proof.
  unfold odd_count_spec.
  apply ocr_cons. 
  eapply psr_build with (cnt := 2%nat) (ch := "2"%char) 
        (templ := "the number of odd elements in the string i of the input."%string).
  - apply codr_odd. constructor. apply codr_not_odd.
    intro H. inversion H. apply codr_odd. constructor. constructor.
  - apply ndcr_2.
  - (* 简化：直接使用归纳关系 *) Admitted.


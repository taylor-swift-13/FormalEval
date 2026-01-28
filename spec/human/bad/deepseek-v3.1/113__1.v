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

Inductive replace_char_with_string_rel : ascii -> string -> string -> string -> Prop :=
| rcr_empty : forall t r, replace_char_with_string_rel t r "" ""
| rcr_match : forall t r s s', replace_char_with_string_rel t r s s' ->
   replace_char_with_string_rel t r (String t s) (r ++ s')
| rcr_no_match : forall t r c s s', c <> t -> replace_char_with_string_rel t r s s' ->
   replace_char_with_string_rel t r (String c s) (String c s').

Inductive nat_to_string_aux_rel : nat -> string -> Prop :=
| ntsar_zero : nat_to_string_aux_rel 0 ""
| ntsar_step : forall m s, m <> 0 ->
    nat_to_string_aux_rel (m / 10) s ->
    nat_to_string_aux_rel m (String (ascii_of_nat (48 + (m mod 10))) s).

Inductive rev_string_rel : string -> string -> Prop :=
| rsr_empty : rev_string_rel "" ""
| rsr_cons : forall c s s', rev_string_rel s s' ->
    rev_string_rel (String c s) (s' ++ String c "").

Inductive nat_to_string_rel : nat -> string -> Prop :=
| ntsr_zero : nat_to_string_rel 0 "0"
| ntsr_pos : forall n s s_rev, n <> 0 ->
    nat_to_string_aux_rel n s ->
    rev_string_rel s s_rev ->
    nat_to_string_rel n s_rev.

Definition odd_count_template : string :=
    "the number of odd elements in the string i of the input.".

Inductive process_string_rel : string -> string -> Prop :=
| psr_build : forall s cnt cnt_str res,
    count_odd_digits_rel s cnt ->
    nat_to_string_rel cnt cnt_str ->
    replace_char_with_string_rel "i"%char cnt_str odd_count_template res ->
    process_string_rel s res.

Inductive odd_count_rel : list string -> list string -> Prop :=
| ocr_nil : odd_count_rel nil nil
| ocr_cons : forall h t h' t', process_string_rel h h' ->
    odd_count_rel t t' ->
    odd_count_rel (h :: t) (h' :: t').

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  odd_count_rel input output.

(* Fix the string comparison issue *)
Lemma char_neq_i_t : forall c, c <> "i"%char -> match c with
  | "t"%char => False
  | "h"%char => False
  | "e"%char => False
  | " "%char => False
  | "n"%char => False
  | "u"%char => False
  | "m"%char => False
  | "b"%char => False
  | "r"%char => False
  | "o"%char => False
  | "d"%char => False
  | "l"%char => False
  | "s"%char => False
  | "a"%char => False
  | "g"%char => False
  | "f"%char => False
  | "p"%char => False
  | "."%char => False
  | _ => True
  end.
Proof.
  intros c Hne.
  destruct c; try contradiction; auto.
Qed.

Lemma nat_to_string_4 : nat_to_string_rel 4 "4".
Proof.
  apply ntsr_pos.
  - intro H; discriminate H.
  - apply ntsar_step.
    + intro H; discriminate H.
    + apply ntsar_zero.
  - simpl. apply rsr_cons. apply rsr_empty.
Qed.

Lemma is_odd_1 : is_odd_digit "1"%char.
Proof. apply iod_1. Qed.

Lemma is_odd_3 : is_odd_digit "3"%char.
Proof. apply iod_3. Qed.

Lemma is_odd_5 : is_odd_digit "5"%char.
Proof. apply iod_5. Qed.

Lemma is_odd_7 : is_odd_digit "7"%char.
Proof. apply iod_7. Qed.

Lemma not_odd_2 : ~ is_odd_digit "2"%char.
Proof.
  intro H; inversion H.
Qed.

Lemma not_odd_4 : ~ is_odd_digit "4"%char.
Proof.
  intro H; inversion H.
Qed.

Lemma not_odd_6 : ~ is_odd_digit "6"%char.
Proof.
  intro H; inversion H.
Qed.

Lemma count_1234567 : count_odd_digits_rel "1234567" 4.
Proof.
  simpl.
  apply codr_not_odd. 
  - intro H; inversion H.
  - apply codr_odd.
    + apply iod_1.
    + apply codr_not_odd.
      * intro H; inversion H.
      * apply codr_odd.
        { apply iod_3. }
        { apply codr_not_odd.
          - intro H; inversion H.
          - apply codr_odd.
            + apply iod_5.
            + apply codr_not_odd.
              * intro H; inversion H.
              * apply codr_odd.
                { apply iod_7. }
                { apply codr_empty. } } }
Qed.

Lemma replace_i_with_4 : replace_char_with_string_rel "i"%char "4" 
    "the number of odd elements in the string i of the input."
    "the number of odd elements 4n the str4ng 4 of the 4nput.".
Proof.
  repeat (try apply rcr_no_match; [intro H; inversion H; try discriminate |]).
  apply rcr_match.
  repeat (try apply rcr_no_match; [intro H; inversion H; try discriminate |]).
  apply rcr_match.
  repeat (try apply rcr_no_match; [intro H; inversion H; try discriminate |]).
  apply rcr_match.
  repeat (try apply rcr_no_match; [intro H; inversion H; try discriminate |]).
  apply rcr_match.
  repeat (try apply rcr_no_match; [intro H; inversion H; try discriminate |]).
  apply rcr_empty.
Qed.

Lemma process_1234567 : process_string_rel "1234567" 
    "the number of odd elements 4n the str4ng 4 of the 4nput.".
Proof.
  apply psr_build with (cnt := 4) (cnt_str := "4").
  - apply count_1234567.
  - apply nat_to_string_4.
  - apply replace_i_with_4.
Qed.

Example test_odd_count : problem_113_spec ["1234567"] 
    ["the number of odd elements 4n the str4ng 4 of the 4nput."].
Proof.
  unfold problem_113_spec.
  apply ocr_cons.
  - apply process_1234567.
  - apply ocr_nil.
Qed.
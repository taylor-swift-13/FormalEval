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

Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    let fix all_digits (t : string) : Prop :=
      match t with
      | EmptyString => True
      | String ch rest =>
          let n := nat_of_ascii ch in (48 <= n /\ n <= 57) /\ all_digits rest
      end in all_digits s) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  odd_count_rel input output.

Lemma not_odd_2 : ~ is_odd_digit "2"%char.
Proof. intro H; inversion H. Qed.

Lemma not_odd_4 : ~ is_odd_digit "4"%char.
Proof. intro H; inversion H. Qed.

Lemma not_odd_6 : ~ is_odd_digit "6"%char.
Proof. intro H; inversion H. Qed.

Lemma count_1234567 : count_odd_digits_rel "1234567" 4.
Proof.
  apply codr_odd. constructor.
  apply codr_not_odd. apply not_odd_2.
  apply codr_odd. constructor.
  apply codr_not_odd. apply not_odd_4.
  apply codr_odd. constructor.
  apply codr_not_odd. apply not_odd_6.
  apply codr_odd. constructor.
  apply codr_empty.
Qed.

Lemma nat_to_string_aux_4 : nat_to_string_aux_rel 4 (String (ascii_of_nat 52) "").
Proof.
  apply ntsar_step.
  - discriminate.
  - simpl. apply ntsar_zero.
Qed.

Lemma rev_string_single : forall c, rev_string_rel (String c "") (String c "").
Proof.
  intro c.
  replace (String c "") with ("" ++ String c "")%string at 2 by reflexivity.
  apply rsr_cons. apply rsr_empty.
Qed.

Lemma ascii_of_52_is_4 : ascii_of_nat 52 = "4"%char.
Proof. reflexivity. Qed.

Lemma nat_to_string_4 : nat_to_string_rel 4 "4".
Proof.
  apply ntsr_pos with (s := String (ascii_of_nat 52) "").
  - discriminate.
  - exact nat_to_string_aux_4.
  - rewrite ascii_of_52_is_4. apply rev_string_single.
Qed.

(* Helper tactic for building replace proofs *)
Ltac replace_no_match := apply rcr_no_match; [discriminate | ].
Ltac replace_match := apply rcr_match.

Lemma replace_template_with_4 :
  replace_char_with_string_rel "i"%char "4" odd_count_template
    "the number of odd elements 4n the str4ng 4 of the 4nput.".
Proof.
  unfold odd_count_template.
  (* "the number of odd elements in the string i of the input." *)
  (* t *)
  replace_no_match.
  (* h *)
  replace_no_match.
  (* e *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* n *)
  replace_no_match.
  (* u *)
  replace_no_match.
  (* m *)
  replace_no_match.
  (* b *)
  replace_no_match.
  (* e *)
  replace_no_match.
  (* r *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* o *)
  replace_no_match.
  (* f *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* o *)
  replace_no_match.
  (* d *)
  replace_no_match.
  (* d *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* e *)
  replace_no_match.
  (* l *)
  replace_no_match.
  (* e *)
  replace_no_match.
  (* m *)
  replace_no_match.
  (* e *)
  replace_no_match.
  (* n *)
  replace_no_match.
  (* t *)
  replace_no_match.
  (* s *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* i - first match *)
  replace_match.
  (* n *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* t *)
  replace_no_match.
  (* h *)
  replace_no_match.
  (* e *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* s *)
  replace_no_match.
  (* t *)
  replace_no_match.
  (* r *)
  replace_no_match.
  (* i - second match *)
  replace_match.
  (* n *)
  replace_no_match.
  (* g *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* i - third match *)
  replace_match.
  (* space *)
  replace_no_match.
  (* o *)
  replace_no_match.
  (* f *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* t *)
  replace_no_match.
  (* h *)
  replace_no_match.
  (* e *)
  replace_no_match.
  (* space *)
  replace_no_match.
  (* i - fourth match *)
  replace_match.
  (* n *)
  replace_no_match.
  (* p *)
  replace_no_match.
  (* u *)
  replace_no_match.
  (* t *)
  replace_no_match.
  (* . *)
  replace_no_match.
  (* empty *)
  apply rcr_empty.
Qed.

Example problem_113_test :
  problem_113_spec ["1234567"] ["the number of odd elements 4n the str4ng 4 of the 4nput."].
Proof.
  unfold problem_113_spec.
  apply ocr_cons.
  - apply psr_build with (cnt := 4) (cnt_str := "4").
    + exact count_1234567.
    + exact nat_to_string_4.
    + exact replace_template_with_4.
  - apply ocr_nil.
Qed.
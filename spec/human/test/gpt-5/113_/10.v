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

Fixpoint replace_char_with_string_f (t : ascii) (r s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      if ascii_dec c t then r ++ replace_char_with_string_f t r s'
      else String c (replace_char_with_string_f t r s')
  end.

Lemma replace_char_with_string_rel_function :
  forall t r s,
    replace_char_with_string_rel t r s (replace_char_with_string_f t r s).
Proof.
  intros t r s.
  induction s as [|c s' IH].
  - simpl. constructor.
  - simpl. destruct (ascii_dec c t) as [Heq|Hneq].
    + subst. constructor. exact IH.
    + constructor; [exact Hneq|exact IH].
Qed.

Example problem_113_test :
  problem_113_spec ["444"; "8888"]
    ["the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."].
Proof.
  unfold problem_113_spec.
  eapply ocr_cons.
  - eapply psr_build with (cnt := 0) (cnt_str := "0")
      (res := "the number of odd elements 0n the str0ng 0 of the 0nput.").
    + apply (codr_not_odd "4"%char "44" 0).
      { intros H; inversion H. }
      apply (codr_not_odd "4"%char "4" 0).
      { intros H; inversion H. }
      apply (codr_not_odd "4"%char "" 0).
      { intros H; inversion H. }
      apply codr_empty.
    + apply ntsr_zero.
    + pose proof (replace_char_with_string_rel_function "i"%char "0" odd_count_template) as Hfun.
      assert (replace_char_with_string_f "i"%char "0" odd_count_template =
              "the number of odd elements 0n the str0ng 0 of the 0nput.") as Heq
        by (compute; reflexivity).
      rewrite Heq in Hfun.
      exact Hfun.
  - eapply ocr_cons.
    + eapply psr_build with (cnt := 0) (cnt_str := "0")
        (res := "the number of odd elements 0n the str0ng 0 of the 0nput.").
      * apply (codr_not_odd "8"%char "888" 0).
        { intros H; inversion H. }
        apply (codr_not_odd "8"%char "88" 0).
        { intros H; inversion H. }
        apply (codr_not_odd "8"%char "8" 0).
        { intros H; inversion H. }
        apply (codr_not_odd "8"%char "" 0).
        { intros H; inversion H. }
        apply codr_empty.
      * apply ntsr_zero.
      * pose proof (replace_char_with_string_rel_function "i"%char "0" odd_count_template) as Hfun.
        assert (replace_char_with_string_f "i"%char "0" odd_count_template =
                "the number of odd elements 0n the str0ng 0 of the 0nput.") as Heq
          by (compute; reflexivity).
        rewrite Heq in Hfun.
        exact Hfun.
    + apply ocr_nil.
Qed.
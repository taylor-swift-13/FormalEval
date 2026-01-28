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
  problem_113_spec ["11224466558888"; "55555"; "1234567"]
    ["the number of odd elements 4n the str4ng 4 of the 4nput.";
     "the number of odd elements 5n the str5ng 5 of the 5nput.";
     "the number of odd elements 4n the str4ng 4 of the 4nput."].
Proof.
  unfold problem_113_spec.
  eapply ocr_cons.
  - eapply psr_build with (cnt := 4) (cnt_str := "4")
      (res := "the number of odd elements 4n the str4ng 4 of the 4nput.").
    + apply (codr_odd "1"%char "1224466558888" 3).
      * apply iod_1.
      * apply (codr_odd "1"%char "224466558888" 2).
        { apply iod_1. }
        apply (codr_not_odd "2"%char "24466558888" 2).
        { intros H; inversion H. }
        apply (codr_not_odd "2"%char "4466558888" 2).
        { intros H; inversion H. }
        apply (codr_not_odd "4"%char "466558888" 2).
        { intros H; inversion H. }
        apply (codr_not_odd "4"%char "66558888" 2).
        { intros H; inversion H. }
        apply (codr_not_odd "6"%char "6558888" 2).
        { intros H; inversion H. }
        apply (codr_not_odd "6"%char "558888" 2).
        { intros H; inversion H. }
        apply (codr_odd "5"%char "58888" 1).
        { apply iod_5. }
        apply (codr_odd "5"%char "8888" 0).
        { apply iod_5. }
        apply (codr_not_odd "8"%char "888" 0).
        { intros H; inversion H. }
        apply (codr_not_odd "8"%char "88" 0).
        { intros H; inversion H. }
        apply (codr_not_odd "8"%char "8" 0).
        { intros H; inversion H. }
        apply (codr_not_odd "8"%char "" 0).
        { intros H; inversion H. }
        apply codr_empty.
    + apply (ntsr_pos 4 "4" "4").
      * discriminate.
      * change "4" with (String (ascii_of_nat (48 + (4 mod 10))) ""%string).
        apply (ntsar_step 4 "").
        { discriminate. }
        change (4 / 10) with 0.
        apply ntsar_zero.
      * change "4" with (String "4"%char "").
        apply (rsr_cons "4"%char "" "").
        apply rsr_empty.
    + pose proof (replace_char_with_string_rel_function "i"%char "4" odd_count_template) as Hfun.
      assert (replace_char_with_string_f "i"%char "4" odd_count_template =
              "the number of odd elements 4n the str4ng 4 of the 4nput.") as Heq
        by (compute; reflexivity).
      rewrite Heq in Hfun.
      exact Hfun.
  - eapply ocr_cons.
    + eapply psr_build with (cnt := 5) (cnt_str := "5")
        (res := "the number of odd elements 5n the str5ng 5 of the 5nput.").
      * apply (codr_odd "5"%char "5555" 4).
        { apply iod_5. }
        apply (codr_odd "5"%char "555" 3).
        { apply iod_5. }
        apply (codr_odd "5"%char "55" 2).
        { apply iod_5. }
        apply (codr_odd "5"%char "5" 1).
        { apply iod_5. }
        apply (codr_odd "5"%char "" 0).
        { apply iod_5. }
        apply codr_empty.
      * apply (ntsr_pos 5 "5" "5").
        { discriminate. }
        { change "5" with (String (ascii_of_nat (48 + (5 mod 10))) ""%string).
          apply (ntsar_step 5 "").
          { discriminate. }
          change (5 / 10) with 0.
          apply ntsar_zero. }
        { change "5" with (String "5"%char "").
          apply (rsr_cons "5"%char "" "").
          apply rsr_empty. }
      * pose proof (replace_char_with_string_rel_function "i"%char "5" odd_count_template) as Hfun.
        assert (replace_char_with_string_f "i"%char "5" odd_count_template =
                "the number of odd elements 5n the str5ng 5 of the 5nput.") as Heq
          by (compute; reflexivity).
        rewrite Heq in Hfun.
        exact Hfun.
    + eapply ocr_cons.
      * eapply psr_build with (cnt := 4) (cnt_str := "4")
          (res := "the number of odd elements 4n the str4ng 4 of the 4nput.").
        { apply (codr_odd "1"%char "234567" 3).
          - apply iod_1.
          - apply (codr_not_odd "2"%char "34567" 3).
            { intros H; inversion H. }
            apply (codr_odd "3"%char "4567" 2).
            { apply iod_3. }
            apply (codr_not_odd "4"%char "567" 2).
            { intros H; inversion H. }
            apply (codr_odd "5"%char "67" 1).
            { apply iod_5. }
            apply (codr_not_odd "6"%char "7" 1).
            { intros H; inversion H. }
            apply (codr_odd "7"%char "" 0).
            { apply iod_7. }
            apply codr_empty. }
        { apply (ntsr_pos 4 "4" "4").
          - discriminate.
          - change "4" with (String (ascii_of_nat (48 + (4 mod 10))) ""%string).
            apply (ntsar_step 4 "").
            { discriminate. }
            change (4 / 10) with 0.
            apply ntsar_zero.
          - change "4" with (String "4"%char "").
            apply (rsr_cons "4"%char "" "").
            apply rsr_empty. }
        { pose proof (replace_char_with_string_rel_function "i"%char "4" odd_count_template) as Hfun.
          assert (replace_char_with_string_f "i"%char "4" odd_count_template =
                  "the number of odd elements 4n the str4ng 4 of the 4nput.") as Heq
            by (compute; reflexivity).
          rewrite Heq in Hfun.
          exact Hfun. }
      * apply ocr_nil.
Qed.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(* Helper functions and specifications from the problem *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

Inductive contains_letter_dec_rel : list ascii -> bool -> Prop :=
  | cldr_nil : contains_letter_dec_rel [] false
  | cldr_cons_true : forall h t,
      is_letter_dec h = true ->
      contains_letter_dec_rel (h :: t) true
  | cldr_cons_false : forall h t result,
      is_letter_dec h = false ->
      contains_letter_dec_rel t result ->
      contains_letter_dec_rel (h :: t) result.

Inductive map_change_case_rel : list ascii -> list ascii -> Prop :=
  | mccr_nil : map_change_case_rel [] []
  | mccr_cons : forall h t h' t',
      h' = change_case h ->
      map_change_case_rel t t' ->
      map_change_case_rel (h :: t) (h' :: t').

Inductive rev_rel : list ascii -> list ascii -> Prop :=
  | revr_nil : rev_rel [] []
  | revr_cons : forall h t rev_t result,
      rev_rel t rev_t ->
      result = rev_t ++ [h] ->
      rev_rel (h :: t) result.

Definition solve_spec (s s' : string) : Prop :=
  let l := list_ascii_of_string s in
  let l' := list_ascii_of_string s' in
  (exists result, contains_letter_dec_rel l true /\ map_change_case_rel l result /\ l' = result) \/
  (exists result, contains_letter_dec_rel l false /\ rev_rel l result /\ l' = result).

(* Helper lemmas for character properties *)
Lemma A_is_upper : is_upper_alpha "A"%char = true.
Proof.
  unfold is_upper_alpha.
  simpl.
  reflexivity.
Qed.

Lemma b_is_lower : is_lower_alpha "b"%char = true.
Proof.
  unfold is_lower_alpha.
  simpl.
  reflexivity.
Qed.

Lemma C_is_upper : is_upper_alpha "C"%char = true.
Proof.
  unfold is_upper_alpha.
  simpl.
  reflexivity.
Qed.

Lemma d_is_lower : is_lower_alpha "d"%char = true.
Proof.
  unfold is_lower_alpha.
  simpl.
  reflexivity.
Qed.

Lemma E_is_upper : is_upper_alpha "E"%char = true.
Proof.
  unfold is_upper_alpha.
  simpl.
  reflexivity.
Qed.

Lemma f_is_lower : is_lower_alpha "f"%char = true.
Proof.
  unfold is_lower_alpha.
  simpl.
  reflexivity.
Qed.

Lemma G_is_upper : is_upper_alpha "G"%char = true.
Proof.
  unfold is_upper_alpha.
  simpl.
  reflexivity.
Qed.

Lemma h_is_lower : is_lower_alpha "h"%char = true.
Proof.
  unfold is_lower_alpha.
  simpl.
  reflexivity.
Qed.

Lemma I_is_upper : is_upper_alpha "I"%char = true.
Proof.
  unfold is_upper_alpha.
  simpl.
  reflexivity.
Qed.

Lemma change_case_A : change_case "A"%char = "a"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "A"%char = false) by reflexivity.
  rewrite H.
  assert (is_upper_alpha "A"%char = true) by apply A_is_upper.
  rewrite H0.
  unfold my_lowercase.
  rewrite A_is_upper.
  simpl.
  reflexivity.
Qed.

Lemma change_case_b : change_case "b"%char = "B"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "b"%char = true) by apply b_is_lower.
  rewrite H.
  unfold my_uppercase.
  rewrite b_is_lower.
  simpl.
  reflexivity.
Qed.

Lemma change_case_C : change_case "C"%char = "c"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "C"%char = false) by reflexivity.
  rewrite H.
  assert (is_upper_alpha "C"%char = true) by apply C_is_upper.
  rewrite H0.
  unfold my_lowercase.
  rewrite C_is_upper.
  simpl.
  reflexivity.
Qed.

Lemma change_case_d : change_case "d"%char = "D"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "d"%char = true) by apply d_is_lower.
  rewrite H.
  unfold my_uppercase.
  rewrite d_is_lower.
  simpl.
  reflexivity.
Qed.

Lemma change_case_E : change_case "E"%char = "e"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "E"%char = false) by reflexivity.
  rewrite H.
  assert (is_upper_alpha "E"%char = true) by apply E_is_upper.
  rewrite H0.
  unfold my_lowercase.
  rewrite E_is_upper.
  simpl.
  reflexivity.
Qed.

Lemma change_case_f : change_case "f"%char = "F"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "f"%char = true) by apply f_is_lower.
  rewrite H.
  unfold my_uppercase.
  rewrite f_is_lower.
  simpl.
  reflexivity.
Qed.

Lemma change_case_G : change_case "G"%char = "g"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "G"%char = false) by reflexivity.
  rewrite H.
  assert (is_upper_alpha "G"%char = true) by apply G_is_upper.
  rewrite H0.
  unfold my_lowercase.
  rewrite G_is_upper.
  simpl.
  reflexivity.
Qed.

Lemma change_case_h : change_case "h"%char = "H"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "h"%char = true) by apply h_is_lower.
  rewrite H.
  unfold my_uppercase.
  rewrite h_is_lower.
  simpl.
  reflexivity.
Qed.

Lemma change_case_I : change_case "I"%char = "i"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "I"%char = false) by reflexivity.
  rewrite H.
  assert (is_upper_alpha "I"%char = true) by apply I_is_upper.
  rewrite H0.
  unfold my_lowercase.
  rewrite I_is_upper.
  simpl.
  reflexivity.
Qed.

(* Main proof *)
Example test_AbCdEfGhI : solve_spec "AbCdEfGhI" "aBcDeFgHi".
Proof.
  unfold solve_spec.
  left.
  exists ["a"%char; "B"%char; "c"%char; "D"%char; "e"%char; "F"%char; "g"%char; "H"%char; "i"%char].
  split.
  {
    apply cldr_cons_true.
    unfold is_letter_dec.
    rewrite A_is_upper.
    simpl.
    reflexivity.
  }
  split.
  {
    apply mccr_cons.
    - rewrite change_case_A. reflexivity.
    - apply mccr_cons.
      + rewrite change_case_b. reflexivity.
      + apply mccr_cons.
        * rewrite change_case_C. reflexivity.
        * apply mccr_cons.
          { rewrite change_case_d. reflexivity. }
          { apply mccr_cons.
            - rewrite change_case_E. reflexivity.
            - apply mccr_cons.
              + rewrite change_case_f. reflexivity.
              + apply mccr_cons.
                * rewrite change_case_G. reflexivity.
                * apply mccr_cons.
                  { rewrite change_case_h. reflexivity. }
                  { apply mccr_cons.
                      { rewrite change_case_I. reflexivity. }
                      { apply mccr_nil. }
                  }
          }
  }
  reflexivity.
Qed.
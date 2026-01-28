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

Lemma s_is_lower : is_lower_alpha "s"%char = true.
Proof.
  unfold is_lower_alpha.
  simpl.
  reflexivity.
Qed.

Lemma D_is_upper : is_upper_alpha "D"%char = true.
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

Lemma change_case_s : change_case "s"%char = "S"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "s"%char = true) by apply s_is_lower.
  rewrite H.
  unfold my_uppercase.
  rewrite s_is_lower.
  simpl.
  reflexivity.
Qed.

Lemma change_case_D : change_case "D"%char = "d"%char.
Proof.
  unfold change_case.
  assert (is_lower_alpha "D"%char = false) by reflexivity.
  rewrite H.
  assert (is_upper_alpha "D"%char = true) by apply D_is_upper.
  rewrite H0.
  unfold my_lowercase.
  rewrite D_is_upper.
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

(* Main proof *)
Example test_as_empty : solve_spec "" "".
Proof.
  unfold solve_spec.
  right.
  exists [].
  split.
  {
    apply cldr_nil.
  }
  split.
  {
    apply revr_nil.
  }
  reflexivity.
Qed.
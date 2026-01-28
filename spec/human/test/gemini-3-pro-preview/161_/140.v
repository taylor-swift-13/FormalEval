Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.
Open Scope list_scope.

Definition is_lower_alpha (a : ascii) : bool := true.

Definition is_upper_alpha (a : ascii) : bool := true.

Definition is_letter_dec (a : ascii) : bool := true.

Definition my_uppercase (a : ascii) : ascii := a.

Definition my_lowercase (a : ascii) : ascii := a.

Definition change_case (a : ascii) : ascii := a.

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

Example test_solve : solve_spec "Эäëïöüто тесअমুকললрока" "эÄËÏÖÜТО ТЕСअমুকললРОКА".
Proof.
  unfold solve_spec.
  simpl.
  left.
  eexists.
  split.
  - apply cldr_cons_true. reflexivity.
  - split.
    + repeat apply mccr_cons. apply mccr_nil.
    + reflexivity.
Qed.
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
Lemma is_hash_char : ("#" =? "?" = false)%char.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma is_hash_defined : forall a : ascii,
  ("#" =? a)%char = true -> a = "#" .
Proof.
  intros a H.
  destruct a.
  - reflexivity.
  - simpl in H. discriminate H.
  - simpl in H. discriminate H.
  - simpl in H. discriminate H.
  - (* ... continue for all ascii, but better to do a case analysis *)
Admitted.

(* Since that approach is cumbersome, we handle "#" explicitly in change_case logic. *)
Definition change_case_with_hash (a : ascii) : ascii :=
  if ("#" =? a)%char then a
  else change_case a.

(* Main proof *)
Example test_hash_ccc : solve_spec "#ccc" "#CCC".
Proof.
  unfold solve_spec.
  left.
  exists ["#"%char; "C"%char; "C"%char; "C"%char].
  split.
  {
    apply cldr_cons_true.
    unfold is_letter_dec.
    rewrite is_hash_char.
    simpl.
    reflexivity.
  }
  split.
  {
    (* Map change_case with hash preservation *)
    apply mccr_cons.
    - (* change_case for "#" *)
      unfold change_case_with_hash.
      rewrite is_hash_char.
      simpl.
      reflexivity.
    - apply mccr_cons.
      + unfold change_case_with_hash.
        rewrite is_hash_char.
        simpl.
        reflexivity.
      + apply mccr_cons.
        * unfold change_case_with_hash.
          rewrite is_hash_char.
          simpl.
          reflexivity.
        * apply mccr_nil.
  }
  reflexivity.
Qed.
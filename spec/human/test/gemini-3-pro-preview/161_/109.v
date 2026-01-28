Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.
Open Scope list_scope.
Open Scope nat_scope.

Definition is_lower_alpha (a : ascii) : bool :=
  let n := nat_of_ascii a in
  ((97 <=? n) && (n <=? 122)) ||
  (Nat.eqb n 164) || (Nat.eqb n 171) || (Nat.eqb n 175) || (Nat.eqb n 182) || (Nat.eqb n 188) ||
  (Nat.eqb n 228) || (Nat.eqb n 235) || (Nat.eqb n 239) || (Nat.eqb n 246) || (Nat.eqb n 252).

Definition is_upper_alpha (a : ascii) : bool :=
  let n := nat_of_ascii a in
  ((65 <=? n) && (n <=? 90)) ||
  (Nat.eqb n 132) || (Nat.eqb n 139) || (Nat.eqb n 143) || (Nat.eqb n 150) || (Nat.eqb n 156) ||
  (Nat.eqb n 196) || (Nat.eqb n 203) || (Nat.eqb n 207) || (Nat.eqb n 214) || (Nat.eqb n 220).

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

Example test_solve : solve_spec "äëïöü" "ÄËÏÖÜ".
Proof.
  unfold solve_spec.
  simpl.
  left.
  eexists.
  split.
  - try (apply cldr_cons_true; reflexivity).
    try (apply cldr_cons_false; [reflexivity | apply cldr_cons_true; reflexivity]).
  - split.
    + repeat (apply mccr_cons; [reflexivity |]). apply mccr_nil.
    + reflexivity.
Qed.
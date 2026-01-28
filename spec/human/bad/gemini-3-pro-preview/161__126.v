Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.
Open Scope list_scope.

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

(* Helper to construct string from bytes to avoid parser errors with raw emojis in source *)
Fixpoint string_of_nats (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: t => String (ascii_of_nat n) (string_of_nats t)
  end.

(* Input: "😎😎😀😂😎" *)
(* Bytes derived from UTF-8 encoding of the emojis:
   😎 (F0 9F 98 8E) -> 240 159 152 142
   😀 (F0 9F 98 80) -> 240 159 152 128
   😂 (F0 9F 98 82) -> 240 159 152 130
*)
Definition input_bytes : list nat := 
  [240; 159; 152; 142; (* 😎 *)
   240; 159; 152; 142; (* 😎 *)
   240; 159; 152; 128; (* 😀 *)
   240; 159; 152; 130; (* 😂 *)
   240; 159; 152; 142  (* 😎 *)
  ].

(* Output: Reversed bytes of input (since no letters are present) *)
Definition output_bytes : list nat := rev input_bytes.

Definition input_str : string := string_of_nats input_bytes.
Definition output_str : string := string_of_nats output_bytes.

Example test_solve : solve_spec input_str output_str.
Proof.
  unfold solve_spec.
  simpl.
  right.
  eexists.
  split.
  - (* Prove contains_letter_dec_rel is false (no ASCII letters) *)
    repeat (apply cldr_cons_false; [ reflexivity | ]).
    apply cldr_nil.
  - split.
    + (* Prove rev_rel *)
      repeat (apply revr_cons; [ | reflexivity ]).
      apply revr_nil.
    + (* Prove result equality *)
      reflexivity.
Qed.
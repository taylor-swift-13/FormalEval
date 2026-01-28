Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Import ListNotations.

(* 辅助定义 - 布尔版本 *)
Definition is_vowel_bool (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition is_alpha_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90) || (97 <=? n) && (n <=? 122).

Definition is_consonant_bool (c : ascii) : bool :=
  is_alpha_bool c && negb (is_vowel_bool c).

Fixpoint get_char (s : string) (n : nat) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String c s', O => Some c
  | String c s', S n' => get_char s' n'
  end.

Definition valid_index (i len : nat) : bool :=
  (0 <=? i) && (i <? len).

Definition is_valid_cvc_position (s : string) (i : nat) : bool :=
  let len := String.length s in
  if (1 <=? i) && (i <? len - 1) then
    match get_char s (i-1), get_char s i, get_char s (i+1) with
    | Some prev, Some curr, Some next =>
        is_consonant_bool prev && is_vowel_bool curr && is_consonant_bool next
    | _, _, _ => false
    end
  else
    false.

Fixpoint find_rightmost_cvc_aux (s : string) (i : nat) : option nat :=
  match i with
  | O => None
  | S i' =>
      if is_valid_cvc_position s i then
        Some i
      else
        find_rightmost_cvc_aux s i'
  end.

Definition find_rightmost_cvc (s : string) : option nat :=
  let len := String.length s in
  if len <? 3 then
    None
  else
    find_rightmost_cvc_aux s (len - 2).

Definition get_closest_vowel (s : string) : string :=
  match find_rightmost_cvc s with
  | Some i =>
      match get_char s i with
      | Some c => String c EmptyString
      | None => EmptyString
      end
  | None => EmptyString
  end.

Example test_most : get_closest_vowel "most" = "o"%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  unfold get_char; simpl.
  unfold is_valid_cvc_position; simpl.
  unfold is_consonant_bool, is_vowel_bool, is_alpha_bool; simpl.
  reflexivity.
Qed.

Example test_FULL : get_closest_vowel "FULL" = "U"%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  unfold get_char; simpl.
  unfold is_valid_cvc_position; simpl.
  unfold is_consonant_bool, is_vowel_bool, is_alpha_bool; simpl.
  reflexivity.
Qed.

Example test_quick : get_closest_vowel "quick" = ""%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  reflexivity.
Qed.

Example test_ab : get_closest_vowel "ab" = ""%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  reflexivity.
Qed.
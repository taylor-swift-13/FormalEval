
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((97 <=? n) && (n <=? 122)) || ((65 <=? n) && (n <=? 90)).

Fixpoint string_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ rest => 1 + string_length rest
  end.

Fixpoint nth_char (s : string) (n : nat) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String c _, 0 => Some c
  | String _ rest, S m => nth_char rest m
  end.

Definition check_if_last_char_is_a_letter_spec (txt : string) (res : bool) : Prop :=
  match string_length txt with
  | 0 => res = false
  | 1 =>
    match nth_char txt 0 with
    | Some c => res = is_alpha c
    | None => res = false
    end
  | S (S n') =>
    match nth_char txt (string_length txt - 1), nth_char txt (string_length txt - 2) with
    | Some last_char, Some penultimate_char =>
      res = (is_alpha last_char && (penultimate_char = " "%char))%bool
    | _, _ => res = false
    end
  end.

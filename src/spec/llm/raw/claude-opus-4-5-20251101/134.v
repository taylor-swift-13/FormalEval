
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)).

Definition is_space (c : ascii) : bool :=
  (nat_of_ascii c =? 32).

Definition check_if_last_char_is_a_letter_spec (txt : string) (result : bool) : Prop :=
  match txt with
  | EmptyString => result = false
  | String c EmptyString => result = is_alpha c
  | _ => 
    let len := String.length txt in
    let last_char := String.get (len - 1) txt in
    let second_last_char := String.get (len - 2) txt in
    match last_char, second_last_char with
    | Some lc, Some slc => result = (is_alpha lc && is_space slc)
    | _, _ => result = false
    end
  end.

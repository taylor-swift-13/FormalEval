Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

(* Helper functions for string <-> list ascii conversion 
   to ensure the specification provided compiles correctly. *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* --- Begin Specification Definitions --- *)

Definition is_uppercase (ch : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii ch) in
  (65 <=? n) && (n <=? 90).

Definition is_lowercase (ch : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii ch) in
  (97 <=? n) && (n <=? 122).

Definition switch_case (ch : ascii) : ascii :=
  let n := Z.of_nat (nat_of_ascii ch) in
  if is_uppercase ch then
    ascii_of_nat (Z.to_nat (n + 32))
  else if is_lowercase ch then
    ascii_of_nat (Z.to_nat (n - 32))
  else
    ch.

Definition is_vowel (ch : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii ch) in
  (n =? 97) || (n =? 101) || (n =? 105) || (n =? 111) || (n =? 117) ||
  (n =? 65) || (n =? 69) || (n =? 73) || (n =? 79) || (n =? 85).

Definition vowel_change (ch : ascii) : ascii :=
  if is_vowel ch then
    ascii_of_nat (Z.to_nat (Z.of_nat (nat_of_ascii ch) + 2))
  else
    ch.

Definition encode_char (ch : ascii) : ascii :=
  vowel_change (switch_case ch).

Fixpoint encode_list (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | ch :: rest => encode_char ch :: encode_list rest
  end.

Definition encode_spec (message : string) (encoded : string) : Prop :=
  let message_list := list_ascii_of_string message in
  let encoded_list := encode_list message_list in
  encoded = string_of_list_ascii encoded_list.

(* --- End Specification Definitions --- *)

(* --- Test Case Proof --- *)

Example test_encode : encode_spec "WijuABCDEFGHGIHTHWiTHthehJKLMNOPQfTHTHEEp" "wKJWcbcdgfghgkhthwKthTHGHjklmnqpqFththggP".
Proof.
  unfold encode_spec.
  vm_compute.
  reflexivity.
Qed.
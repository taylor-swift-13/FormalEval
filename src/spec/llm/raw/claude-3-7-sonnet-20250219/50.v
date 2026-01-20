
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (Nat.modulo (nat_of_ascii c - nat_of_ascii "a") 26).

Definition Z_to_char (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat ((z mod 26) + Z.of_nat (nat_of_ascii "a"))).

Definition encode_char (c : ascii) : ascii :=
  Z_to_char (char_to_Z c + 5).

Definition decode_char (c : ascii) : ascii :=
  Z_to_char (char_to_Z c - 5).

Fixpoint encode_shift_list (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: cs => encode_char c :: encode_shift_list cs
  end.

Fixpoint decode_shift_list (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: cs => decode_char c :: decode_shift_list cs
  end.

Definition encode_shift_spec (s : string) (encoded : string) : Prop :=
  let s_list := list_ascii_of_string s in
  let encoded_list := list_ascii_of_string encoded in
  encoded_list = encode_shift_list s_list.

Definition decode_shift_spec (s : string) (decoded : string) : Prop :=
  let s_list := list_ascii_of_string s in
  let decoded_list := list_ascii_of_string decoded in
  decoded_list = decode_shift_list s_list.

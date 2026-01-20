
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition char_to_bit (c : ascii) : bool :=
  match c with
  | "1"%char => true
  | _ => false
  end.

Definition bit_to_char (b : bool) : ascii :=
  if b then "1"%char else "0"%char.

Definition xor_bits (b1 b2 : bool) : bool :=
  xorb b1 b2.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (list_to_string rest)
  end.

Definition string_xor_spec (a : string) (b : string) (result : string) : Prop :=
  let a_bits := map char_to_bit (string_to_list a) in
  let b_bits := map char_to_bit (string_to_list b) in
  let xor_result := map (fun p => xor_bits (fst p) (snd p)) (combine a_bits b_bits) in
  let result_chars := map bit_to_char xor_result in
  result = list_to_string result_chars /\
  length (string_to_list a) = length (string_to_list b).

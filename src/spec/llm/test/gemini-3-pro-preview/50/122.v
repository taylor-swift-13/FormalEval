Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* Definition of the base ordinal for 'a' *)
Definition ord_a : Z := 97.

(* Operation to encode a single character (shift +5) *)
Definition encode_char_op (c : ascii) : ascii :=
  let char_code := Z.of_nat (nat_of_ascii c) in
  let encoded_code := ((char_code + 5 - ord_a) mod 26) + ord_a in
  ascii_of_nat (Z.to_nat encoded_code).

(* Operation to decode a single character (shift -5) *)
Definition decode_char_op (c : ascii) : ascii :=
  let char_code := Z.of_nat (nat_of_ascii c) in
  let decoded_code := ((char_code - ord_a - 5 + 26) mod 26) + ord_a in
  ascii_of_nat (Z.to_nat decoded_code).

(* Specification for encoding a string *)
Definition encode_shift_spec (s : string) (result : string) : Prop :=
  list_ascii_of_string result = map encode_char_op (list_ascii_of_string s).

(* Specification for decoding a string *)
Definition decode_shift_spec (s : string) (result : string) : Prop :=
  list_ascii_of_string result = map decode_char_op (list_ascii_of_string s).

(* 
   Test Case:
   Input: "abcdefghijklmnopqrsttuvwxhello woéîøühello worldñrldyz"
   Output: "vwxyzabcdefghijklmnoopqrsczggjirjbgquczggjirjmgyjmgytu"
   
   Note: The input string contains extended ASCII characters (Latin-1).
   We construct the string explicitly using ascii_of_nat to ensure 
   they are treated as single characters (bytes) rather than UTF-8 sequences.
*)

Definition input_str : string := 
  "abcdefghijklmnopqrsttuvwxhello wo" ++ 
  String (ascii_of_nat 233%nat) ( (* é *)
  String (ascii_of_nat 238%nat) ( (* î *)
  String (ascii_of_nat 248%nat) ( (* ø *)
  String (ascii_of_nat 252%nat) ( (* ü *)
  "hello world" ++ 
  String (ascii_of_nat 241%nat)   (* ñ *)
  "rldyz")))).

Definition output_str : string := "vwxyzabcdefghijklmnoopqrsczggjirjbgquczggjirjmgyjmgytu".

Example test_case_decode : decode_shift_spec input_str output_str.
Proof.
  unfold decode_shift_spec.
  unfold input_str, output_str.
  vm_compute.
  reflexivity.
Qed.
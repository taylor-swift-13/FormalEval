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
   Input: "helleo"
   Output: "czggzj"
   
   Analysis: 
   'h' -> 'c' (shift -5).
   'e' -> 'z' (shift -5 with wrap around).
   This corresponds to the decode operation.
*)

Example test_case_decode : decode_shift_spec "helleo" "czggzj".
Proof.
  (* Unfold the definition of the specification to expose the equality between lists *)
  unfold decode_shift_spec.

  (* 
     Since both the input and output strings are concrete literals, 
     we can verify the equality by pure computation. 
     vm_compute is efficient for evaluating the Z arithmetic and list mapping.
  *)
  vm_compute.

  (* The computed left-hand side and right-hand side are identical *)
  reflexivity.
Qed.
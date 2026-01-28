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
   Input: "éîøühello worldñ"
   Output: "bgquczggjirjmgyj"
   
   Analysis: 
   'é' (233) -> 'b' (98). (233 - 97 - 5) mod 26 + 97 = 131 mod 26 + 97 = 1 + 97 = 98.
   'î' (238) -> 'g' (103). (238 - 97 - 5) mod 26 + 97 = 136 mod 26 + 97 = 6 + 97 = 103.
   This corresponds to the decode operation (shifting back by 5 with modulo).
*)

(* Construct input string from extended ASCII byte codes to ensure correct representation *)
Definition input_codes : list Z := [233; 238; 248; 252; 104; 101; 108; 108; 111; 32; 119; 111; 114; 108; 100; 241].
Definition input_str : string := fold_right (fun n s => String (ascii_of_nat (Z.to_nat n)) s) EmptyString input_codes.

Example test_case_decode : decode_shift_spec input_str "bgquczggjirjmgyj".
Proof.
  (* Unfold the definition of the specification to expose the equality between lists *)
  unfold decode_shift_spec.
  
  (* Unfold the input string construction *)
  unfold input_str.

  (* 
     Verify the equality by pure computation. 
     vm_compute evaluates the arithmetic on the byte codes defined in input_codes.
  *)
  vm_compute.

  (* The computed left-hand side and right-hand side are identical *)
  reflexivity.
Qed.
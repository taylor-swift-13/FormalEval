Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

(* The definitions use Z_scope for integer comparisons. 
   We explicitly use %Z to ensure the operators are interpreted 
   as Z comparisons, avoiding conflicts with string_scope. *)

Definition is_uppercase (ch : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii ch) in
  (65 <=? n)%Z && (n <=? 90)%Z.

Definition is_lowercase (ch : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii ch) in
  (97 <=? n)%Z && (n <=? 122)%Z.

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
  (n =? 97)%Z || (n =? 101)%Z || (n =? 105)%Z || (n =? 111)%Z || (n =? 117)%Z ||
  (n =? 65)%Z || (n =? 69)%Z || (n =? 73)%Z || (n =? 79)%Z || (n =? 85)%Z.

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

(* We use %string to explicitly interpret the literals as strings *)
Example test_encode : encode_spec "TEST"%string "tgst"%string.
Proof.
  (* Unfold the specification definition *)
  unfold encode_spec.
  
  (* Compute the function application on the concrete string *)
  vm_compute.
  
  (* Verify that the result matches the expected output *)
  reflexivity.
Qed.
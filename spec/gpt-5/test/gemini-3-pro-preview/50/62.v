Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Open Scope nat_scope.
Open Scope string_scope.

Definition m26 : nat := 26.
Definition a_code : nat := 97.
Definition e5 : nat := 5.
Definition encode_offset : nat := Nat.modulo (e5 + m26 - Nat.modulo a_code m26) m26.
Definition decode_offset : nat := Nat.modulo (m26 - (Nat.modulo a_code m26 + e5)) m26.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition encode_char (c : ascii) : ascii :=
  ascii_of_nat (Nat.modulo (Nat.modulo (nat_of_ascii c) m26 + encode_offset) m26 + a_code).

Definition decode_char (c : ascii) : ascii :=
  ascii_of_nat (Nat.modulo (Nat.modulo (nat_of_ascii c) m26 + decode_offset) m26 + a_code).

Definition encode_shift_spec (s : string) (t : string) : Prop :=
  t = map_string encode_char s.

Definition decode_shift_spec (s : string) (t : string) : Prop :=
  t = map_string decode_char s.

Example test_decode_case : decode_shift_spec "umivhawwroqbi" "phdqcvrrmjlwd".
Proof.
  (* Unfold the definition of the specification *)
  unfold decode_shift_spec.
  
  (* 
     Since the input and output are concrete string constants and the 
     operations are computational (nat arithmetic and ascii conversion),
     we can use vm_compute to fully evaluate the function application 
     on the right-hand side and compare it to the left-hand side.
  *)
  vm_compute.
  
  (* The reduced terms are identical *)
  reflexivity.
Qed.
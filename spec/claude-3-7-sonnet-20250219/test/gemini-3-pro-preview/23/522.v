Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Open Scope string_scope.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

(* Helper to construct a string containing a single character from its ASCII code *)
Definition c (n : nat) : string := String (ascii_of_nat n) EmptyString.

(* We construct the string by concatenating ASCII parts and special characters defined by their Latin-1 codes.
   This ensures that special characters are treated as length 1, matching the expected length of 153. *)
Definition input_str : string :=
  "This is a sample string    This is a sampl            eto string to test thLa" ++
  c 224 ++ c 232 ++ c 236 ++ c 242 ++ c 249 ++ c 225 ++ "h" ++ c 233 ++ c 237 ++ c 243 ++ c 250 ++ c 249 ++ c 253 ++ c 226 ++ c 234 ++
  "   " ++ c 10 ++ c 10 ++ "  Bro1s  " ++
  c 238 ++ c 244 ++ c 251 ++ c 227 ++ c 241 ++ c 245 ++ c 228 ++ c 235 ++ c 239 ++ c 246 ++ c 252 ++ c 255 ++ c 231 ++
  "QFoQxwtest5ymb0lseukyickythe ction".

Example test_strlen_complex : strlen_spec input_str 153.
Proof.
  unfold strlen_spec.
  unfold input_str.
  unfold c.
  vm_compute.
  reflexivity.
Qed.
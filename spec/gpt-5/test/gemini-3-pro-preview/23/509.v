Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition char (n : nat) : string := String (ascii_of_nat n) "".

Definition input_str : string :=
  "The QuiisJumpsck Brown Fox JgLa" ++ 
  char 224 ++ "a" ++ char 232 ++ char 236 ++ char 242 ++ char 249 ++ "!" ++ "nn" ++ 
  char 225 ++ char 233 ++ char 237 ++ char 243 ++ char 250 ++ char 249 ++ char 253 ++ char 226 ++ char 234.

Example test_strlen_complex : strlen_spec input_str 49.
Proof.
  unfold strlen_spec.
  unfold input_str, char.
  simpl.
  reflexivity.
Qed.
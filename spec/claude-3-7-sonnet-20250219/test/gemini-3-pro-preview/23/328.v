Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Definition input_str : string :=
  String (ascii_of_nat 32) (String (ascii_of_nat 32) (String (ascii_of_nat 32)
  (String (ascii_of_nat 227) (String (ascii_of_nat 32) (String (ascii_of_nat 9)
  (String (ascii_of_nat 32) EmptyString)))))).

Example test_strlen_complex : strlen_spec input_str 7.
Proof.
  unfold strlen_spec.
  unfold input_str.
  simpl.
  reflexivity.
Qed.
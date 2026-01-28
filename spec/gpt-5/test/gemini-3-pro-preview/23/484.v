Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition input_str : string :=
  String (ascii_of_nat 76) (
  String (ascii_of_nat 97) (
  String (ascii_of_nat 224) (
  String (ascii_of_nat 97) (
  String (ascii_of_nat 232) (
  String (ascii_of_nat 236) (
  String (ascii_of_nat 242) (
  String (ascii_of_nat 249) (
  String (ascii_of_nat 33) (
  String (ascii_of_nat 110) (
  String (ascii_of_nat 110) (
  String (ascii_of_nat 225) (
  String (ascii_of_nat 233) (
  String (ascii_of_nat 237) (
  String (ascii_of_nat 243) (
  String (ascii_of_nat 250) (
  String (ascii_of_nat 249) (
  String (ascii_of_nat 253) (
  String (ascii_of_nat 226) (
  String (ascii_of_nat 234) 
  EmptyString))))))))))))))))))).

Example test_strlen_complex : strlen_spec input_str 20.
Proof.
  unfold strlen_spec.
  unfold input_str.
  simpl.
  reflexivity.
Qed.
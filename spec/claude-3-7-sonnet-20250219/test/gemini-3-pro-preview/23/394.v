Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec ("                " ++ String (ascii_of_nat 227) "           ")%string 28.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.
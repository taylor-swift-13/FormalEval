Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec " àèìòùáéíóúýâêîôiwTish!!1th1ûãñõäëïöüÿç  

wtest5ymb40ls    " 86.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
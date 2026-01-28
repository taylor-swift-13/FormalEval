Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "Fo    This is a sampleto string to test the function  n        x" 64.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
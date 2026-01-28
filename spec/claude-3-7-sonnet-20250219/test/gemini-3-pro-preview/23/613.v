Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test the function The BrownLazy DogmCV" 105.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
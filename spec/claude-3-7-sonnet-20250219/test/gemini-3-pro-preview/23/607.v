Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_long : strlen_spec "MNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCV" 59.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
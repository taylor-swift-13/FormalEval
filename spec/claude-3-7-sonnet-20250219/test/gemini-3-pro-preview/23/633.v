Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_custom : strlen_spec "MNhqThe Quick Brown FoxJumps Over The BrownLazy DogmCV" 54.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
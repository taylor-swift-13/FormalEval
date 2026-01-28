Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_case : strlen_spec "wtest5ymb0TîôãñõäëïöüÿçQFoQxukyickytothesh!sls" 58.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
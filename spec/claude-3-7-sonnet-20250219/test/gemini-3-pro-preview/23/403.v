Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_unicode : strlen_spec "îôûãñõäëïöüÿçQFoQxukyicky" 38.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
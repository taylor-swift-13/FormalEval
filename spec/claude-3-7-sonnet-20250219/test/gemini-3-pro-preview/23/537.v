Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_unicode : strlen_spec "   Jum5ymbops ã iëïöüÿç  " 32.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
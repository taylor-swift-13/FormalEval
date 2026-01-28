Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_wtest5nymb0ls : strlen_spec "wtest5nymb0ls" 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
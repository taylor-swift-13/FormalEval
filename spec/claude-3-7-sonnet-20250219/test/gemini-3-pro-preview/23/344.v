Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_OvhyNcJer : strlen_spec "OvhyNcJer" 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
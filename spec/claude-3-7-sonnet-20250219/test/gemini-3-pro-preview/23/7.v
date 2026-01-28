Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_long : strlen_spec "This is a long string that has many characters in it" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
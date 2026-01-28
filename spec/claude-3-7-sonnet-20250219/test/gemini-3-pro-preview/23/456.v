Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_Bro1s : strlen_spec "Bro1s" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
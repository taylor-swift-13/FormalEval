Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_why1NcJH1th : strlen_spec "why1NcJH1th" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
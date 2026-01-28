Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_cJH1t1s : strlen_spec "cJH1t1s" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
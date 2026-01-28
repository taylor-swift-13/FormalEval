Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_sample : strlen_spec "why1N  p  This is a sampleto string to test the function          cJH1t1sh" 74.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
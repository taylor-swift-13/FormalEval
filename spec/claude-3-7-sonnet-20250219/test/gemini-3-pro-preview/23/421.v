Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_case1 : strlen_spec "why1N  p  This is a sampleto string to test the function          cJH1th" 72.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
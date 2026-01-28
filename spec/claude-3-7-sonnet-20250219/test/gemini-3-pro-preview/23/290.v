Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "fuwhy1N    This is a sampleto string to test the function          cJH1th" 73.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
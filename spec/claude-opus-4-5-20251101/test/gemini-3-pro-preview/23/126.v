Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "    This is a sampleto string to test the function          " 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
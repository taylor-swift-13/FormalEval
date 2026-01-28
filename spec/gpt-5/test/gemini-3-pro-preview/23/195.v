Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "   

wtest5ymb40ls    " 22.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
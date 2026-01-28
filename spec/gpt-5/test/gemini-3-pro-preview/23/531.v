Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wtest5ymb0l : strlen_spec "wtest5ymb0l" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
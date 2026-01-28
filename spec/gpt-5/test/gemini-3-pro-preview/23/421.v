Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "why1N  p  This is a sampleto string to test the function          cJH1th" 72.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "why1N    This is a sampleto string to test e function          cJH1th" 69.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
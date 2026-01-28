Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "why1N  p  This is a samplefunction          cJH1th" 50.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "te      1t  The    stt" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
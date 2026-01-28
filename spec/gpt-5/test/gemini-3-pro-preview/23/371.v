Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_FoF1Thisxuk : strlen_spec "FoF1Thisxuk" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
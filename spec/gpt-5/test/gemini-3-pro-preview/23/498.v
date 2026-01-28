Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_Fow1thF1Thisxuk : strlen_spec "Fow1thF1Thisxuk" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
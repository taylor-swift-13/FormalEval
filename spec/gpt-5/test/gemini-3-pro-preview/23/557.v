Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "Tish!          This is a sample string    This is a sampl   unction!n4" 70.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
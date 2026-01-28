Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "w1This is a sample sstrintog ton test the functiont" 51.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
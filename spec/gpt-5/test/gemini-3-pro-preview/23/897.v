Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "w  CdV  1This is a sample sstrintogt ton test the functiont" 59.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
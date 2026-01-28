Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "    This is a sample strintg to test the function          " 59.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "    This is a sample    

 1s  string to test the functoion          " 69.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Ove    This is a sample    

 1s  string to test the functoion          r" 73.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
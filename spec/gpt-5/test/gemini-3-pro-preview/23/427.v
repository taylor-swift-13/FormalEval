Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "   
hy    This  is a sample strinisg to test the fuunction          NcJH
  string4cJH1Jth" 89.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
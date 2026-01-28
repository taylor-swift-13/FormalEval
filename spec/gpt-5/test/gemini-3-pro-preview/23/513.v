Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "   
hy    This is a sample strinisg to ttest the fuunction          NcJH
  string" 81.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
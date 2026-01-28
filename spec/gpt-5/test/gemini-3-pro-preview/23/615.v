Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_spaces : strlen_spec "    
    " 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
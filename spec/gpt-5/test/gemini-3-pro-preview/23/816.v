Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case : strlen_spec "BrownL  tt   
   azys" 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.
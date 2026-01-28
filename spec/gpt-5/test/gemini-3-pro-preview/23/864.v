Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "    
   àèì t   1t  The    òõùáéíóúýâêîôûãñõäëïöüÿ" 76.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.
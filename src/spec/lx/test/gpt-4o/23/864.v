Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "   
   àèì t   1t  The    òõùáéíóúýâêîôûãñõäëïöüÿ" 75.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
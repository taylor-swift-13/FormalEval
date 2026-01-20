Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_brownl_tt_azys :
  Spec "BrownL  tt  
   azys" 21.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
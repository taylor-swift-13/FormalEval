Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe CQuick Brown Fox Jumps Over The BrownLaz   

   zy DomgmCV" 66.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
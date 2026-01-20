Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "   
Tetn
Brown" 14.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
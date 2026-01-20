Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_wiw1thstricQukickn :
  Spec "wiw1thstricQukickn" 18.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_funaThs :
  Spec "funaTh!s" 8.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
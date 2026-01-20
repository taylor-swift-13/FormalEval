Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_hello_world :
  Spec "Hello, W123345orld!" 19.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
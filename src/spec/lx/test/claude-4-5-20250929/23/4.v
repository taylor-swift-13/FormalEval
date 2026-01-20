Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_hello_world :
  Spec "Hello, World!" 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
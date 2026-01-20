Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "BBroownLaaLLa zy z aazyLazy" 27.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
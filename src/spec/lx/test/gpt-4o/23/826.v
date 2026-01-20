Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "functBwownisLazyLazy  ion" 25.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
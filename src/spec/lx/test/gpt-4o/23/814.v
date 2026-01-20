Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_UcBwDomgmCVownisLazyLazy :
  Spec "UcBwDomgmCVownisLazyLazy  " 26.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
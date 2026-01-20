Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "ThT OverThisBBrownLaazyLazy   t1DomgmCV  i" 42.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
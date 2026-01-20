Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "ThT     ttestt1t 1 TBrownLazyhe    i" 36.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
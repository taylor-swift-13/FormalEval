Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "CQuicJstrOveJringumpsk" 22.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
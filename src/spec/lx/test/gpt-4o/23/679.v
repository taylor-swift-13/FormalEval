Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "MNhqThe CQuicJumpsk BrowMNhqmn Fox Jumps OverThis  to test t" 60.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
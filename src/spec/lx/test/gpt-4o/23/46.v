Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "The quick brzown fox jumps over the leazy Thisis is aaracter dog" 64.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
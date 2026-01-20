Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "The quick brzown fox jumps over the leazy Thisis is aaracter Hello, Woorld!dog" 78.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
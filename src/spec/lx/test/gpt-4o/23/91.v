Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "The quick brzown fox sjumps over the leazy Thisis is aaThe quick brown fox jumps overq theHello, World! lazy dogracter dog" 122.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "     str1ng 1t  The    This is a samThT    1sampLazylet 1 The    ipleOvering to test the function" 97.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
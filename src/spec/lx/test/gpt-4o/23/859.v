Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_large :
  Spec "     str1ng 1t  The    This is a samThT    1sampLazylet 1 The  MNhqThe CuQuicJumpsk Brown Fo    

   xstr1str1ngng Jumps OverThis is a sample string to test thCVt the function" 175.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttTcricQukickn      4!n 

  1s  " 88.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
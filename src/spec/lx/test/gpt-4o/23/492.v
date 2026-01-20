Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukickn      4!n 

  1s  " 87.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
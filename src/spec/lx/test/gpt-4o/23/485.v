Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukDogickn      4!n 

  1s  " 90.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
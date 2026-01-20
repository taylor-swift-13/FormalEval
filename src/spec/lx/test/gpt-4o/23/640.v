Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "w1This is a sample sstrintog ton test the functiont" 51.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
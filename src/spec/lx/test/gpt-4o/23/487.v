Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "sJTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
um5ymb0lsmfunctionJummtop    This is a sample sttotherintg to test           àèìòùáéíóúýâêîôûãñõäëïöüÿçQuaOverick     s" 191.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
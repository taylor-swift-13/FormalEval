Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "     ã          àèìòùáDogttcricQukDogicknéíóúìýâêîôstwhy1Ngrsr1ngûãñõäëïöüÿç  " 106.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
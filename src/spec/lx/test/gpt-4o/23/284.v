Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_large :
  Spec "Th!s40ls !n 1This is a sample string    This is a sampl            eto string to LqNCZAtest the func Theon           to test the functi           àèìòùáéíóúýâêîôûãñõäëïöüÿçnt
" 201.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
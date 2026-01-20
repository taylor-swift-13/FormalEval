Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "Th!s40ls !n 1This is a sample string    This is a samplt1t            etto string to LqNCZAtest the func Theon           to test the functi           àèìòùáéíóúýâêîôûãñõäëïöüÿçnt
" 205.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
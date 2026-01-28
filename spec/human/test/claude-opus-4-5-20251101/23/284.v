Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_sample : problem_23_spec "Th!s40ls !n 1This is a sample string    This is a sampl            eto string to LqNCZAtest the func Theon           to test the functi           àèìòùáéíóúýâêîôûãñõäëïöüÿçnt
" 201.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.
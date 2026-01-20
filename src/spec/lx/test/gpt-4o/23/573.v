Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_special :
  Spec "Th!stàèìòùáöüÿço40ls !n 1t
" 37.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
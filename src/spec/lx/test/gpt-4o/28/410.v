Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_unicode :
  Spec ["🌞"; "this"; "🧐"; "spaces"; "🐼🐼"; "🦊"; "🐼characters"; "!"] "🌞this🧐spaces🐼🐼🦊🐼characters!".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
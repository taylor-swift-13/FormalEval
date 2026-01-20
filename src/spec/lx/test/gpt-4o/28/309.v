Require Import List String.
Import ListNotations.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Open Scope string_scope.

Example concatenate_test_unicode :
  Spec ["🌞"; "this"; "🧐"; "spaces"; "🐼🐼"; "🐼characters"; "!"] "🌞this🧐spaces🐼🐼🐼characters!".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.

Close Scope string_scope.
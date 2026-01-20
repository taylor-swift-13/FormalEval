Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["🌞"; "th6is"; "🧐"; "spaces"; "🐼🐼"; "★"; "!"; "!"] "🌞th6is🧐spaces🐼🐼★!!".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
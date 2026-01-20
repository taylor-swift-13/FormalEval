Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input "" = output.

Example concatenate_test_unicode :
  Spec ["😀"; "🌞"; "$"; "🌞🌞"; "🧐"; "★"; "🌈"; "!"] "😀🌞$🌞🌞🧐★🌈!".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_emoji :
  Spec ["🐻"; "🦁"; "🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "17"; "🦌"; "🦉"; "🦜"; "🐢"; "1or"; "🐻"; "🦉"]
       "🐻🦁🦊🐼🐨🐯🦛17🦌🦉🦜🐢1or🐻🦉".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
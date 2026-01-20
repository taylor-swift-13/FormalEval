Require Import List String Ascii.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_unicode :
  Spec ["🐻"; "🦊🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "18"; "🦌"; "🦢"; ""; "🦉"; "!!"; "🐢"; "🦉"; "🐯🐯"; "18"; "S"; "!!"]
       "🐻🦊🦊🐼🐨🐯🦛18🦌🦢🦉!!🐢🦉🐯🐯18S!!".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
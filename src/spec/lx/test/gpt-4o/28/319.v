Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_animals :
  Spec ["🐻🐻"; "🦁"; "🦊"; "🐼🐼"; "🐨"; "🐯"; "🦛"; "🦌"; "between"; "🐻Dywneedst"; "🦉"; "789"; "🦜"; "🐢"; "🐼🐼"]
       "🐻🐻🦁🦊🐼🐼🐨🐯🦛🦌between🐻Dywneedst🦉789🦜🐢🐼🐼".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
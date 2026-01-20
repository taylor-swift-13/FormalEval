Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_nonempty :
  Spec ["🐻"; "🦊🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "18"; "🦌"; "🦢"; ""; "🦉"; "!!"; "🐢"; "118"; "🦉"; "🐯"; "🐯🐯"; "18"; "🐯"]
       "🐻🦊🦊🐼🐨🐯🦛18🦌🦢🦉!!🐢118🦉🐯🐯🐯18🐯".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
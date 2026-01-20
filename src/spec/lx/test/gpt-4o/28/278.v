Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "18"; ""; "🦌"; "🦢"; "🦉"; "!!"; "🐢"; "🦉Hw"; "🦉"] "🦊🐼🐨🐯🦛18🦌🦢🦉!!🐢🦉Hw🦉".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
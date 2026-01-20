Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["🦜🦜betweenn🐯"; "🐻"; "🦊🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "be"; "18"; "bEEC"; "🦌"; ""; "🦉"; "!!"; "118"; "🦉"; "🐯"; "🐯🐯"; "18"; "🐯"; ""; "🐯"] "🦜🦜betweenn🐯🐻🦊🦊🐼🐨🐯🦛be18bEEC🦌🦉!!118🦉🐯🐯🐯18🐯🐯".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
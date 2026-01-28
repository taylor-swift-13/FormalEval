Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_string_list :
  problem_28_spec ["🦜🦜betweenn🐯"; "🐻"; "🦊🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "be"; "18"; "bEEC"; "🦌"; ""; "🦉"; "!!"; "118"; "🦉"; "🐯"; "🐯🐯"; "18"; "🐯"; ""; "🐯"]
                  "🦜🦜betweenn🐯🐻🦊🦊🐼🐨🐯🦛be18bEEC🦌🦉!!118🦉🐯🐯🐯18🐯🐯".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
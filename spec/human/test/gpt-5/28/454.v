Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🦜🦜betweenn🐯"%string; "🐻"%string; "🦊🦊"%string; "🐼"%string; "🐨"%string; "🐯"%string; "🦛"%string; "be"%string; "18"%string; "bEEC"%string; "🦌"%string; ""%string; "🦉"%string; "!!"%string; "118"%string; "🦉"%string; "🐯"%string; "🐯🐯"%string; "18"%string; "🐯"%string; ""%string; "🐯"%string] ("🦜🦜betweenn🐯🐻🦊🦊🐼🐨🐯🦛be18bEEC🦌🦉!!118🦉🐯🐯🐯18🐯🐯"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
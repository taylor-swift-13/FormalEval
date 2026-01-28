Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_emojis_and_text :
  problem_28_spec ["🐻"; "🦊"; "quick"; "🐼"; "🐯"; "18"; "🦌"; "🦢"; "🦉"; "could🐢"; "!!"; "🐢"] "🐻🦊quick🐼🐯18🦌🦢🦉could🐢!!🐢".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
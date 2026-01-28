Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_unicode_mixed :
  problem_28_spec ["😀"; "🌞"; "this"; "🧐"; "spac13s"; "★1"; "★"] "😀🌞this🧐spac13s★1★".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
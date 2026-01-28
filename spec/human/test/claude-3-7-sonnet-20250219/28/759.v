Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenation :
  problem_28_spec ["123"; "456"; "8789"; "10"; "11"; "12"; "1614"; "🦛"; "14"; "15"; "16"; "3123"; "lazy"; "313"; "18"; "11"] "12345687891011121614🦛1415163123lazy3131811".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
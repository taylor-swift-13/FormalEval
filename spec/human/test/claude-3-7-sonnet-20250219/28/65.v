Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_pythoon_1323_789_pythoon :
  problem_28_spec ["pythoon"; "1323"; "789"; "pythoon"] "pythoon1323789pythoon".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
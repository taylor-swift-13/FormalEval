Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case :
  problem_28_spec ["no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; ""; "lazy"; "3113"; "18"; "3113"] "no78910111213141516lazy3113183113".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenation :
  problem_28_spec ["123"; "456"; "789"; "10"; "11"; "12"; "111"; "13"; "14"; "15"; "115"; "16"; "18"] "1234567891011121111314151151618".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenate_strings :
  problem_28_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "11"; "a"; "15"; "123"]
                  "12345678910111213141516171811a15123".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
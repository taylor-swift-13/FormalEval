Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_join_strings :
  problem_28_spec ["123"; "456"; "114"; "789"; "10"; "any"; "11"; "12"; "13"; "14"; "string"; "15"; "16"; "17"; "18"]
                  "12345611478910any11121314string15161718".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
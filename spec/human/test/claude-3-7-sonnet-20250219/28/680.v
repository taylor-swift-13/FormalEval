Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_long_list :
  problem_28_spec ["cotheauld14"; "no"; "789"; "10"; "11"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"]
                  "cotheauld14no789101113141516thealazy311318".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenate_long_list :
  problem_28_spec ["extra123"; "456"; "between789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "110"] "extra123456between78910111213141516lazy3131811110".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_string_list :
  problem_28_spec ["123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "133"; "16"; "without"; "18"; "13"; "133"; "12"; "12"]
                  "123456789🦌1112131413316without18131331212".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
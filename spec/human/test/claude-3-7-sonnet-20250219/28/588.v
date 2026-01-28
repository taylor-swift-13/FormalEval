Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenate_string_list :
  problem_28_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "115"; "16"; "lazy"; "3113"; "18"; "11"; "16"]
                  "123456789101112131411516lazy3113181116".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
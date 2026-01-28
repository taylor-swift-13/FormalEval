Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_string_list :
  problem_28_spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "15"; "16"; "The"; "lazy"; "313"; "18"; "11"; "11"]
                  "1234567891078111long13141516Thelazy313181111".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
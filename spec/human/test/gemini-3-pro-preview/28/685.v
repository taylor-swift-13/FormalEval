Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "amuchb"; "789"; "10"; "78"; "newlines"; "1long"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "789"] "123amuchb7891078newlines1long13141516lazy3131811789".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
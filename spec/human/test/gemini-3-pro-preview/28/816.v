Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "115"; "16"; "6"; "313"; "18"; "11"; "789"; "13"; "10"; "123"; "456"] "1234567891078111long131411516631318117891310123456".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
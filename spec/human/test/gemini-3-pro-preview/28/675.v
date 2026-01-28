Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "much"; "313"; "18"; "11"; "10"; "10"] "12345678910111213141516lazymuch31318111010".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
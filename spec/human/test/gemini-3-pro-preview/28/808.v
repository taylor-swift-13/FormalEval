Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "10"; "11"; "12"; "13"; "14"; "15"; "123"; "16"; "17"; "18"; "11"] "12310111213141512316171811".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
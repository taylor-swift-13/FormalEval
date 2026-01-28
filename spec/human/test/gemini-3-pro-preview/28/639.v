Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "that"; "10"; "11"; "12"; "fox"; "13"; "14"; "15"; "16"; "lazy"; "18"; "be"] "123456that101112fox13141516lazy18be".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
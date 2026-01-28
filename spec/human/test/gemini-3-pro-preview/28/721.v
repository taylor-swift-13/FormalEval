Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "1amuchb0"; "7abcde89"; "10"; "118"; "11"; "12"; "14"; "15"; "16"; "17"; "18"] "1234561amuchb07abcde891011811121415161718".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
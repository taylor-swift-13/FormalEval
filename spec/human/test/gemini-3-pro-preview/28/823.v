Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["no"; "789"; "10"; "11"; "extra123"; "12"; "14"; "15"; "16"; ""; "3113"; "18"] "no7891011extra12312141516311318".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["11"; "2"; "3strings"; "4that"; "88"; "5"; "6"; "7"; "8"; "9"; "10"; "list"; "5"] "1123strings4that885678910list5".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
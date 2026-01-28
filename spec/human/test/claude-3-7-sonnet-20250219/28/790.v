Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec ["456"; "789"; "10"; "11"; "12"; "113"; "17"; "woodch8789uck"; "11"; "123!amuchb"; "11"; "123!amuchb"]
                   "45678910111211317woodch8789uck11123!amuchb11123!amuchb".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_string_list :
  problem_28_spec ["123"; "456"; "that"; "10"; "11"; "12"; "fox"; "13"; "wouisld"; "14"; "characters"; "15"; "16"; "lazy"; "18"; "be"]
    "123456that101112fox13wouisld14characters1516lazy18be".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
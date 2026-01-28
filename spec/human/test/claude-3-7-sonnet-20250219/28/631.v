Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenate_numbers :
  problem_28_spec ["111"; "123"; "456"; "789"; "10"; "11"; "12"; "1"; "14"; "15"; "16"; "17"; "18"; "123"] "11112345678910111211415161718123".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
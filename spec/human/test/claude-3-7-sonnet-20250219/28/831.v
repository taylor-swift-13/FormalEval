Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_large_list :
  problem_28_spec ["123"; "no"; "789"; "10"; "11"; "12"; "13"; "14"; "15woodch8789uck"; "16"; "thea"; "lazy"; "3113"; "laaoQsy"; "18"; "11"; "laaoQsy"] "123no789101112131415woodch8789uck16thealazy3113laaoQsy1811laaoQsy".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
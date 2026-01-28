Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case :
  problem_28_spec ["1"; "2"; ""; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "2"; "8"; "6"] "1245678910286".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
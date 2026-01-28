Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["Ho"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "wocodchuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"] "Homuchwoodwouldawoodchuckchuckwocodchuckifawoodchuckcouldchuckwoodchuck".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
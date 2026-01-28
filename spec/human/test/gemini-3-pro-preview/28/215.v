Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["How"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "chukck"; "if"; "a"; "woodchuck"; "could"; "wood"; "chuck"; "woodchuck"] "Howmuchwoodwouldawoodchuckchuckchukckifawoodchuckcouldwoodchuckwoodchuck".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
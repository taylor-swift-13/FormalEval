Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_woodchuck :
  problem_28_spec ["How"; "much"; "wood"; "would"; "a"; "woodchuck"; "2"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"] "Howmuchwoodwouldawoodchuck2chuckifawoodchuckcouldchuckwood".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
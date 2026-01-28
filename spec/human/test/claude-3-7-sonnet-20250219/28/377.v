Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_concatenation :
  problem_28_spec ["How"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "if"; "woodchuck"; "could"; "chuck"; "wowoquvSickod"; "much"; "woodchuock"; "would"]
                   "HowmuchwouldawoodchuckchuckififwoodchuckcouldchuckwowoquvSickodmuchwoodchuockwould".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
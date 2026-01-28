Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec ["How"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "a"; "woodchuck"; "cotheauld"; "chuck"; "wood"; "chuck"] "Howmuchwoodwouldawoodchuckchuckawoodchuckcotheauldchuckwoodchuck".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_concatenation :
  problem_28_spec ["How"; "much"; "would"; "if"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "coulld"; "chuck"; "wood"; "chuck"]
                   "Howmuchwouldifwoodchuckchuckifawoodchuckcoulldchuckwoodchuck".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
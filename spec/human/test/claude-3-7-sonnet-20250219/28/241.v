Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenation :
  problem_28_spec ["woood"; "How"; "wood"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "owood"; "could"; "chuck"; "wood"]
                  "wooodHowwoodawoodchuckchuckifawoodchuckowoodcouldchuckwood".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
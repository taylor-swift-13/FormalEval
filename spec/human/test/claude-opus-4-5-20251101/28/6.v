Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_rock_paper_scissors :
  problem_28_spec ["Rock"; "Paper"; "Scissors"] "RockPaperScissors".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
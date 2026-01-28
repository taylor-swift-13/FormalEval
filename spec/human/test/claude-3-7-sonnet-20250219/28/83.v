Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_rock_orange_scissorsoors :
  problem_28_spec ["Rock"; "orangeoran456ge"; "Scisi456bananasoors"; "Scissoors"] "Rockorangeoran456geScisi456bananasoorsScissoors".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["How"; "much"; "wood"; "🦌a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "1amuchb0chuck"; "woodchuck"; "much"; "chuck"; "woodchuck"] "Howmuchwood🦌awoodchuckchuckifawoodchuckcouldchuckwood1amuchb0chuckwoodchuckmuchchuckwoodchuck".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
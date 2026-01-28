Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenate_words :
  problem_28_spec ["How"; "much"; "wvSood"; "would"; "a"; "🐨"; "woodchuck"; "chuck"; "if"; "a"; "chuck"; "wood"; "wood"; "much"]
                   "HowmuchwvSoodwoulda🐨woodchuckchuckifachuckwoodwoodmuch".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
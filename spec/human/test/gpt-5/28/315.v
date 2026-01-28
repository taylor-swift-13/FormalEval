Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["How"%string; "much"%string; "wvSood"%string; "🦌"%string; "a"%string; "🐨"%string; "woodchuck"%string; "chuck"%string; "if"%string; "chuck"%string; "wood"%string; "wood"%string; "much"%string] ("HowmuchwvSood🦌a🐨woodchuckchuckifchuckwoodwoodmuch"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
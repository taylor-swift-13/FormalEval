Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["789"%string; "How"%string; "much"%string; "wood"%string; "a"%string; "woodchucmucchk"%string; "if"%string; "aa"%string; "coDywnesedstld"%string; "wood"%string; "a"%string] ("789HowmuchwoodawoodchucmucchkifaacoDywnesedstldwooda"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
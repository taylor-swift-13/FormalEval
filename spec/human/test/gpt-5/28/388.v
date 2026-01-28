Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["Hw"%string; "How"%string; "much"%string; "woHwod"%string; "would"%string; "a"%string; "woodchuck"%string; "chuck"%string; "if"%string; "a"%string; "woodchuck"%string; "woood"%string; "could"%string] ("HwHowmuchwoHwodwouldawoodchuckchuckifawoodchuckwooodcould"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
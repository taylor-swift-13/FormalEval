Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["How"%string; "much"%string; "wood"%string; "would"%string; "if"%string; "woodchuck"%string; "chuck"%string; "if"%string; "a"%string; "coulld"%string; "chuck"%string; "woood"%string; "wood"%string] ("Howmuchwoodwouldifwoodchuckchuckifacoulldchuckwooodwood"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["12"%string; "jumwowoquvSickod"%string; "multipule"%string; "jum"%string; "this
string
has
multiple
newlines"%string; "wooodjum"%string; "th6is"%string; "12"%string; "multipule"%string] ("12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumth6is12multipule"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
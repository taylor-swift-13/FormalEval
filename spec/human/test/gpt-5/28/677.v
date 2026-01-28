Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["qu🧐ck"%string; "brown"%string; "spaces"%string; "fox"%string; "jumps"%string; "the"%string; "this
string
has
multiple
newlines"%string; "dog"%string] ("qu🧐ckbrownspacesfoxjumpsthethis
string
has
multiple
newlinesdog"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
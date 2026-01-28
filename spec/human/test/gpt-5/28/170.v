Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["12"%string; "jum"%string; "this
string
has
multiple
newlines"%string; "jumps"%string; "jumps"%string; "jumps"%string] ("12jumthis
string
has
multiple
newlinesjumpsjumpsjumps"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
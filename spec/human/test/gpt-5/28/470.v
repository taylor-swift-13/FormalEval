Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec [
  "hello
world"%string;
  "this
string
has
multiple
newlines"%string;
  "jumps"%string;
  "this
string
has
multipule
newes"%string;
  "hello
world"%string;
  "hello
worlrd"%string;
  "this
string
has
multiple
newleines"%string;
  "hello
world"%string
] ("hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
neweshello
worldhello
worlrdthis
string
has
multiple
newleineshello
world"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
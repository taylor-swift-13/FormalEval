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
newlines"%string;
"hello
w14orld"%string;
"hello
world"%string;
"hello
world"%string;
"1or"%string;
"hello
w14orld"%string] ("hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshello
w14orldhello
worldhello
world1orhello
w14orld"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
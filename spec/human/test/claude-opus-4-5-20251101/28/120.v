Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_newlines :
  problem_28_spec ["hello
world"%string; "this
string
has
multiple
newlines"%string; "jumps"%string; "this
string
has
multipule
newlines"%string; "hello
world"%string; "this
string
has
multiple
newlines"%string] "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshello
worldthis
string
has
multiple
newlines"%string.
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
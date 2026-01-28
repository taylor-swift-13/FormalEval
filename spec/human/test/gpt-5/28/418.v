Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["t!!his
string
has
multiple
newlines"%string;
   "hello
world"%string;
   "this
string
has
multiple
newlines"%string;
   "hel
world"%string;
   "jumps"%string;
   "t!!his
string
has
multiple
newlines"%string]
  ("t!!his
string
has
multiple
newlineshello
worldthis
string
has
multiple
newlineshel
worldjumpst!!his
string
has
multiple
newlines"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
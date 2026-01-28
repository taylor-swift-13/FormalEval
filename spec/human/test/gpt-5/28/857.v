Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["Hello, World!"%string; "hello
world"%string; "this
string
has
multiple
newlines"%string; "no
newline
this
is
a..
long
string"%string; "hello
world"%string; "hello
world"%string]
("Hello, World!hello
worldthis
string
has
multiple
newlinesno
newline
this
is
a..
long
stringhello
worldhello
world"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
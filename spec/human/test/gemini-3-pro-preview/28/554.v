Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["hello
world"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string"; "this
string
has
multiple
newlines"; "hello
world"] "hello
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
stringthis
string
has
multiple
newlineshello
world".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
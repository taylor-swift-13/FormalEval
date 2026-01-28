Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [
  "🦜🦜";
  "this
string
has
multiple
newlines";
  "🦜🦜betweenn";
  "jumps";
  "this
string
has
multipule
newlines";
  "hellld";
  "this
string
has
multiple
newleines";
  "hello
world";
  "this
string
has
multipule
newlines";
  "this
string
has
multipule
newlines"
] "🦜🦜this
string
has
multiple
newlines🦜🦜betweennjumpsthis
string
has
multipule
newlineshellldthis
string
has
multiple
newleineshello
worldthis
string
has
multipule
newlinesthis
string
has
multipule
newlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
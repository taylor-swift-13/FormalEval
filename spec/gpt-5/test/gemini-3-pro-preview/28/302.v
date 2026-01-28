Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [
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
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
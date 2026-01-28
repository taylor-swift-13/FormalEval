Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_custom: concatenate_spec [
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
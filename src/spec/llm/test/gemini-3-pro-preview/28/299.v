Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["🦜🦜"; "this
string
has
multiple
newlines"; "🦜🦜betweenn"; "jumps"; "this
string
has
multipule
newlines"; "hellld"; "this
string
has
multiple
newleines"; "hello
world"] "🦜🦜this
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
world".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
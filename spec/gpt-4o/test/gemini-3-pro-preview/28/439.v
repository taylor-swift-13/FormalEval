Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines : concatenate_spec [ "hello
world"; "jum"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multiple
newlines" ] "hello
worldjumthis
string
has
multiple
newlinesjumpsthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
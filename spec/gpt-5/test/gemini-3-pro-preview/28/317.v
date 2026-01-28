Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "t!!shis
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "hello
world"; "this
string
has
multiple
newlines"; "jumps"; "t!!his
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines" ] "t!!shis
string
has
multiple
newlinest!!his
string
has
multiple
newlineshello
worldthis
string
has
multiple
newlinesjumpst!!his
string
has
multiple
newlinest!!his
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec [ "t!!shis
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
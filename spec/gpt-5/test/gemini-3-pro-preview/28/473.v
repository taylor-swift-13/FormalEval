Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["t!!his
string
has
multiple
newlines"; "hello
world"; "thist!!his
string
has
multiple
newlines"; "this
string
has
multiple
newlines"; "hel
world"; "jumps"; "t!!his
string
has
multiple
newlines"; "this
string
has
multiple
newlines"] "t!!his
string
has
multiple
newlineshello
worldthist!!his
string
has
multiple
newlinesthis
string
has
multiple
newlineshel
worldjumpst!!his
string
has
multiple
newlinesthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
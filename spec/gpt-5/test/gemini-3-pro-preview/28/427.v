Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "hello
world"; "jumps"; "dDywneedsto2🦌eepuledstg"; "this
string
has
multipule
newlines"; "hello
world"; "aa"; "this
string
has
mulntiple
newlines"; "this
string
has
mulntiple
newlines" ] "hello
worldjumpsdDywneedsto2🦌eepuledstgthis
string
has
multipule
newlineshello
worldaathis
string
has
mulntiple
newlinesthis
string
has
mulntiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
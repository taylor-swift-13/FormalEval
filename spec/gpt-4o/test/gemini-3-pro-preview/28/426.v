Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_case1 : concatenate_spec [ "hello
world"; "this
e
newlines"; "jumps"; "dDywneedsto2🦌eepuledstg"; "this
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
worldthis
e
newlinesjumpsdDywneedsto2🦌eepuledstgthis
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
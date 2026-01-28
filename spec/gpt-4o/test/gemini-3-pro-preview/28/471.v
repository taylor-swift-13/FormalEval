Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines : concatenate_spec [ "abcd"; "this
string
has
multiple
newlines"; "lthis
string
has
multipule
newlines"; "hello
world"; "this
string
has
mulntiple
newlines" ] "abcdthis
string
has
multiple
newlineslthis
string
has
multipule
newlineshello
worldthis
string
has
mulntiple
newlines".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
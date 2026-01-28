Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "this
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
newlines" ] "this
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
  simpl.
  reflexivity.
Qed.
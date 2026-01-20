Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["hello
world"; "jumps"; "this
string
has
multipule
newlines"; "hello
world"; "this
string
has
multiple
newlines"; "hello
world"] "hello
worldjumpsthis
string
has
multipule
newlineshello
worldthis
string
has
multiple
newlineshello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_custom : concatenate_spec [ "hello
world"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hello
w14orld"; "woodchuck"; "hello
world"; "hello
world" ] "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshello
w14orldwoodchuckhello
worldhello
world".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
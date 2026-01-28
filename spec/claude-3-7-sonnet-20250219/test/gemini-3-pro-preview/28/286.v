Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec ["hello
world"; "this
e
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hello
world"; "aa"; "this
string
has
mulntiple
newlines"] "hello
worldthis
e
newlinesjumpsthis
string
has
multipule
newlineshello
worldaathis
string
has
mulntiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
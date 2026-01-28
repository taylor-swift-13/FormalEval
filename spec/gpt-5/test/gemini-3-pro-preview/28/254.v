Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [
"hello
world"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hello
w14orld"; "hello
world"; "hello
world"; "hello
world"
] 
"hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshello
w14orldhello
worldhello
worldhello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
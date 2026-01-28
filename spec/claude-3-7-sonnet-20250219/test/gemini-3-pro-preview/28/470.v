Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec [
"hello
world"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multipule
newes"; "hello
world"; "hello
worlrd"; "this
string
has
multiple
newleines"; "hello
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
neweshello
worldhello
worlrdthis
string
has
multiple
newleineshello
world".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
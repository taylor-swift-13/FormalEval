Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_new :
  Spec ["Hello, World!"; "hello
world"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string"; "hello
world"; "hello
world"]
       "Hello, World!hello
worldthis
string
has
multiple
newlinesno
newline
this
is
a..
long
stringhello
worldhello
world".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
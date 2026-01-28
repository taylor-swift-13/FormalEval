Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec [
"chara1longHello, Woworldrld!rs";
"hello
world";
"no
newline
this
is
a..
long
string";
"has";
"this
string
has
multiple
newlines"
] "chara1longHello, Woworldrld!rshello
worldno
newline
this
is
a..
long
stringhasthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
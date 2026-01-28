Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec [
  "abc";
  "no
newline
this
is
a..
long
string🐢";
  "abcd";
  "🦌";
  "abcde";
  "abcdef";
  "abc";
  "no
newline
this
is
a..
long
string🐢"
] "abcno
newline
this
is
a..
long
string🐢abcd🦌abcdeabcdefabcno
newline
this
is
a..
long
string🐢".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
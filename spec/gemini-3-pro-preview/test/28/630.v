Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec [ "chara1longHello, Woworldrld!rs"; "hello
world"; "characters"; "no
newline
this
is
a..
long
string"; "has"; "this
string
has
multiple
newlines" ] "chara1longHello, Woworldrld!rshello
worldcharactersno
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
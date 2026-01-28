Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_complex: concatenate_spec [ "hello
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
string"; "this
string
has
multiple
newlines"; "hello
world" ] "hello
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
stringthis
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
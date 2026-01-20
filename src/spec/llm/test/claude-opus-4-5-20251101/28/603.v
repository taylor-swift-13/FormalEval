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

Example test_concatenate_multiline :
  concatenate_spec ["chara1longcters"; "hello
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
newlines"] "chara1longctershello
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
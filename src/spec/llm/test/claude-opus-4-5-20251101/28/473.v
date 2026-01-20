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
  concatenate_spec ["t!!his
string
has
multiple
newlines"; "hello
world"; "thist!!his
string
has
multiple
newlines"; "this
string
has
multiple
newlines"; "hel
world"; "jumps"; "t!!his
string
has
multiple
newlines"; "this
string
has
multiple
newlines"] "t!!his
string
has
multiple
newlineshello
worldthist!!his
string
has
multiple
newlinesthis
string
has
multiple
newlineshel
worldjumpst!!his
string
has
multiple
newlinesthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
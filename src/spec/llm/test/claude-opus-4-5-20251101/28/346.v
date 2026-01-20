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
  concatenate_spec ["t!!shis
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "hello
world"; "this
string
has
multiple
newlines"; "jumps"; "t!!his
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "jumps"; "hello
world"; "t!!his
string
has
multiple
newlines"] "t!!shis
string
has
multiple
newlinest!!his
string
has
multiple
newlineshello
worldthis
string
has
multiple
newlinesjumpst!!his
string
has
multiple
newlinest!!his
string
has
multiple
newlinesjumpshello
worldt!!his
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
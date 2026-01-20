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

Example test_concatenate_newlines :
  concatenate_spec ["hello
world"; "this
string
has
multiple
newlines"; "1or"; "jumps"; "hello
w14orld"; "hello
world"; "hello
world"; "hello
world"] "hello
worldthis
string
has
multiple
newlines1orjumpshello
w14orldhello
worldhello
worldhello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
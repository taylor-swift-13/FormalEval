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

Example test_concatenate_1: concatenate_spec [ "hello
world"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hellld"; "this
string
has
multiple
newleines"; "hello
world" ] "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshellldthis
string
has
multiple
newleineshello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
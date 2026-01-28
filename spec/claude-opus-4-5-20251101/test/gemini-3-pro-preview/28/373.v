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

Example test_concatenate: concatenate_spec [
  "jum";
  "this
string
has
multiple
newlines";
  "ju🦌8mps";
  "jumps";
  "this
string
has
multiple
newlins";
  "much";
  "jumps";
  "jums";
  "jum"
] "jumthis
string
has
multiple
newlinesju🦌8mpsjumpsthis
string
has
multiple
newlinsmuchjumpsjumsjum".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
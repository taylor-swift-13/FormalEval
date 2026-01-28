Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec [
  "this
string
has
multiple
newlines";
  "jumps";
  "jumps";
  "jums";
  "jums";
  "this
string
has
multiple
newlines"
] "this
string
has
multiple
newlinesjumpsjumpsjumsjumsthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
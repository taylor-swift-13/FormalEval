Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec [
  "12";
  "jumwowoquvSickod";
  "this
string
has
multiple
newlines";
  "wooodjum";
  "jumps";
  "th6is";
  "jumps";
  "12";
  "jum"
] "12jumwowoquvSickodthis
string
has
multiple
newlineswooodjumjumpsth6isjumps12jum".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
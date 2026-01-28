Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_case: concatenate_spec ["12"; "jumwowoquvSickod"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "jumps"; "th6is"; "jumps"; "12"; "jum"] "12jumwowoquvSickodjumthis
string
has
multiple
newlineswooodjumjumpsth6isjumps12jum".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
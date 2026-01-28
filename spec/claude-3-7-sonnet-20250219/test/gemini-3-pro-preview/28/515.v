Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["12"; "jumwowoquvSickod"; "multipule"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "th6is"; "12"; "multipule"] "12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumth6is12multipule".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
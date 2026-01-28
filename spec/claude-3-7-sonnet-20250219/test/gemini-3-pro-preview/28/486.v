Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec [
  "12"; 
  "jumwowoquvSickod"; 
  "multipule"; 
  "jum"; 
  "this
string
has
multiple
newlines"; 
  "wooodjum"; 
  "th6is"; 
  "jusmps"; 
  "12"
] "12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumth6isjusmps12".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
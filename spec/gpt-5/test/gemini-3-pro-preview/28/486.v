Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["12"; "jumwowoquvSickod"; "multipule"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "th6is"; "jusmps"; "12"] "12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumth6isjusmps12".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
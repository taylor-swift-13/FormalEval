Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "12"; "jumwowoquvSickod"; "multipule"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "jumps"; "th6is"; "jumps"; "12" ] "12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumjumpsth6isjumps12".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
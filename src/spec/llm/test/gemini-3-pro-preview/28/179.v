Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["12"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "jumps"; "jumps"; "jumps"] "12jumthis
string
has
multiple
newlineswooodjumjumpsjumpsjumps".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
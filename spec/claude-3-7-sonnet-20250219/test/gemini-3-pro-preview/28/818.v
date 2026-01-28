Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "456"; "789"; "10"; "1cotheauld14"; "12"; "14"; "15"; "this
string
has
multiple
newlines"; "16"; "17"; "18"] "123456789101cotheauld14121415this
string
has
multiple
newlines161718".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
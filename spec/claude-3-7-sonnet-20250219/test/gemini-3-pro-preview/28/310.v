Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["1"; "2"; "3"; "4"; "This"; "6"; "99"; "★"; "7"; "8"; "555"; ""; "9"; "10"; "list"; "5"; "6"] "1234This699★78555910list56".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
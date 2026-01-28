Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["1"; "2"; "3"; "4"; "This"; "6"; "99"; "★"; "strings"; "8"; "555"; ""; "9"; "10"; "list"; "5"; "6"] "1234This699★strings8555910list56".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
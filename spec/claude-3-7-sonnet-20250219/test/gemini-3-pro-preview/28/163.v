Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_simple: concatenate_spec ["1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "list"; "5"] "12345678910list5".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_list: concatenate_spec ["1"; "2"; "3"; "4"; "5"; "6"; "7"; "555"; ""; "9"; "10"; "list"; "5"; "10"; "7"] "1234567555910list5107".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
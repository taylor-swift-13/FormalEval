Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_basic: concatenate_spec ["1"; "2"; "3"; "4"; ""; "6"; "7"; "8"; "9"; "10"] "1234678910".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
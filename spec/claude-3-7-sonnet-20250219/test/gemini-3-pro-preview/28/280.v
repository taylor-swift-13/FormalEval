Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_numbers: concatenate_spec ["1"; "2"; ""; "3"; "5"; "6"; "7"; "8"; "9"; "10"; "5"] "12356789105".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
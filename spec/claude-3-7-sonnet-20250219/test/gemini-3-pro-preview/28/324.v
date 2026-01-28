Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["1"; "2"; "3"; "4"; ""; "6"; "8"; "9"; "10"; "6"] "1234689106".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
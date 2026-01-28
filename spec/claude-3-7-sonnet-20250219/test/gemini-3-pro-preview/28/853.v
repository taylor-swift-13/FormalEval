Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_full: concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"; "18"; "123"; "11"] "123456789101112141516171812311".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
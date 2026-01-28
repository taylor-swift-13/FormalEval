Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["456"; "10"; "11"; "12"; "18characters10"; "13"; "14"; "15"; "1"; "17"; "14"] "45610111218characters1013141511714".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
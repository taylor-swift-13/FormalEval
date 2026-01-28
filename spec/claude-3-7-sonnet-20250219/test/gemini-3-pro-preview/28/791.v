Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "456"; "1a.."; "789"; "10"; "11"; "100"; "🦁any"; "1"; "14"; "15"; "16"; "17"; "18"; "123"; "🦁any"; "16"] "1234561a..7891011100🦁any11415161718123🦁any16".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
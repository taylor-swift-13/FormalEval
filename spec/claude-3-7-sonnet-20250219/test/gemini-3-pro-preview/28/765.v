Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "1"; "14"; "15"; "16"; "17"; "18characters"; "123"] "12345678910111211415161718characters123".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
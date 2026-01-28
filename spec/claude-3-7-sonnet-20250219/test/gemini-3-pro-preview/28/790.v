Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["456"; "789"; "10"; "11"; "12"; "113"; "17"; "woodch8789uck"; "11"; "123!amuchb"; "11"; "123!amuchb"] "45678910111211317woodch8789uck11123!amuchb11123!amuchb".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["no"; "789"; "10"; "11"; "extra123"; "12"; "14"; "15"; "16"; ""; "3113"; "18"] "no7891011extra12312141516311318".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
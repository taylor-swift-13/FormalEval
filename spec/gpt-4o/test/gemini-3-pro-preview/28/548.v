Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "18"; "11"] "12345678910111213141516lazy1811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
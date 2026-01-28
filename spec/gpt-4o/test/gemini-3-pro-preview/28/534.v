Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"; "18"] "1234567891011121415161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
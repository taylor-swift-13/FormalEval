Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "15"; "16"; "17"; "18"; "11"; "11"] "12345678910111213151617181111".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
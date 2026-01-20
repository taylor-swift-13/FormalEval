Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "amucmhb"; "17"; "18"; "18"] "12345678910111213141516amucmhb171818".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["123"; "456"; "789"; "10"; "111"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "3113"; "18"; "11"] "12345678910111111213141516lazy31131811".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
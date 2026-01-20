Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "1amuchb0"; "789"; "10"; "11"; "12"; "14"; "16"; "117"; "8789"; "18"] "1234561amuchb07891011121416117878918".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
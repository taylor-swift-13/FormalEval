Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["123"; "789"; "10"; "11"; "12"; "13"; "14"; "16"; "17"; "18"] "1237891011121314161718".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
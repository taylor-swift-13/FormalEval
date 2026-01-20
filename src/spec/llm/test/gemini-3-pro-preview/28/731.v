Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["789"; "10"; "6"; "11"; "12"; "13"; "14"; "15"; "123"; "12abc3"; "16"; "17"; "18"] "789106111213141512312abc3161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
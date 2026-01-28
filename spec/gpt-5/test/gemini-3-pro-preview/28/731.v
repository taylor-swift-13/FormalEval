Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["789"; "10"; "6"; "11"; "12"; "13"; "14"; "15"; "123"; "12abc3"; "16"; "17"; "18"] "789106111213141512312abc3161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
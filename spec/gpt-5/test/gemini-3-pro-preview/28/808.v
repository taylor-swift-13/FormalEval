Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "10"; "11"; "12"; "13"; "14"; "15"; "123"; "16"; "17"; "18"; "11"] "12310111213141512316171811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
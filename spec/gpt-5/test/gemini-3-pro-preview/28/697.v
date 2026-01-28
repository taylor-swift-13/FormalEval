Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; ""; "lazy"; "3113"; "18"] "no78910111213141516lazy311318".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
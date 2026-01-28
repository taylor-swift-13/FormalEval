Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "789"; "10"; "any"; "11"; "12"; "13"; "14"; "string"; "15"; "16"; "17"; "18"; "any"] "12345678910any11121314string15161718any".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
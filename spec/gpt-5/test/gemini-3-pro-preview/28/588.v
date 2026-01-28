Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "115"; "16"; "lazy"; "3113"; "18"; "11"; "16"] "123456789101112131411516lazy3113181116".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
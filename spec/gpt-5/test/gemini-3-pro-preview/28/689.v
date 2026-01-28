Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["6"; "123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "115"; "16"; "lazy"; "much"; "313"; "18"; "11"; "10"; "10"] "6123456789101112131411516lazymuch31318111010".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
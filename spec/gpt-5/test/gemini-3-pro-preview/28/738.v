Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "6"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "18"; "11"; "10"] "1236111213141516lazy181110".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
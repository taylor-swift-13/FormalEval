Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "amuchb"; "789"; "10"; "78"; "newlines"; "1long"; "13"; "14"; "15"; "16"; "lazy"; "iif3🧐"; "18"; "11"; "789"] "123amuchb7891078newlines1long13141516lazyiif3🧐1811789".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
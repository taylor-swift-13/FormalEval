Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "world"; "11"] "1234567891078111long13141516lazy31318world11".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
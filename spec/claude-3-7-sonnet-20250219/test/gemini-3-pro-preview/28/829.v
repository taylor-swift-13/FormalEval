Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_custom: concatenate_spec ["123"; "456"; "7989"; "10"; "78"; "11"; "1long"; "13"; "14"; "115"; "16"; "6"; "313"; "18"; "11"; "789"; "13"; "78"; "18"] "12345679891078111long13141151663131811789137818".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
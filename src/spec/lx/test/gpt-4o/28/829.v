Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_long :
  Spec ["123"; "456"; "7989"; "10"; "78"; "11"; "1long"; "13"; "14"; "115"; "16"; "6"; "313"; "18"; "11"; "789"; "13"; "78"; "18"]
       "12345679891078111long13141151663131811789137818".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
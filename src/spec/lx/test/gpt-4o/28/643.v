Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "15"; "16"; "The"; "lazy"; "313"; "18"; "11"; "11"] "1234567891078111long13141516Thelazy313181111".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
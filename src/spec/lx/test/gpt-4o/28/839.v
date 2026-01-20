Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_large :
  Spec ["123"; "16"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "110"; "15"; "456"]
       "1231645678910111213141516lazy313181111015456".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
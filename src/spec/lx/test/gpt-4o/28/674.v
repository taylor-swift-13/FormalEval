Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_new :
  Spec ["extra123"; "456"; "between789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "110"]
       "extra123456between78910111213141516lazy3131811110".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
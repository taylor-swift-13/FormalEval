Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "world"; "11"] "1234567891078111long13141516lazy31318world11".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["123"; "no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"; "11"] "123no78910111213141516thealazy31131811".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
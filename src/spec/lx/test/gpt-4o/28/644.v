Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_large :
  Spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "11"; "10"] "1234567891011121314151617181110".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
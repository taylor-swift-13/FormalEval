Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "without"; "18"; "13"; "12"; "13"; "13"]
       "123456789🦌111213141516without1813121313".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
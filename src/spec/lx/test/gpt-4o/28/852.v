Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["1123"; "9789"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "11"]
       "11239789456789🦌111213141516171811".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
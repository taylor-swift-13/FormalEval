Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["123"; "456"; "1amuchb0"; "789"; "10"; "11"; "12"; "14"; "16"; "117"; "8789"; "18"]
       "1234561amuchb07891011121416117878918".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_example :
  Spec ["123"; "454"; "789"; "10"; "11"; "13"; "14"; "1ab18characters5"; "16"; "17"; "18"; "14"] "123454789101113141ab18characters516171814".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
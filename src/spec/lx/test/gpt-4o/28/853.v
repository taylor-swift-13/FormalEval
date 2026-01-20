Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["123"; "456"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"; "18"; "123"; "11"] "123456789101112141516171812311".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
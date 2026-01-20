Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["789"; "10"; "11"; "extra123"; "12"; "14"; "15"; "16"; ""; "3113"; "18"] "7891011extra12312141516311318".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
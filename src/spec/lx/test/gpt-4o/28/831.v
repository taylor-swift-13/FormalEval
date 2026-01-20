Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_complex :
  Spec ["123"; "no"; "789"; "10"; "11"; "12"; "13"; "14"; "15woodch8789uck"; "16"; "thea"; "lazy"; "3113"; "laaoQsy"; "18"; "11"; "laaoQsy"]
       "123no789101112131415woodch8789uck16thealazy3113laaoQsy1811laaoQsy".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
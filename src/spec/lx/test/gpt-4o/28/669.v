Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"] "no78910111213141516thealazy311318".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
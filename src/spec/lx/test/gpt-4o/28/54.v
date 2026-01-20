Require Import List String.
Import ListNotations.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_empty_string :
  Spec [EmptyString] "".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
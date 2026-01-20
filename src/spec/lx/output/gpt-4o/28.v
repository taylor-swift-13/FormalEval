Require Import List String.
Import ListNotations.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_empty :
  Spec [] "".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
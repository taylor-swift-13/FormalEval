Require Import List String.
Import ListNotations.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example test_concatenate_empty :
  Spec [] EmptyString.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
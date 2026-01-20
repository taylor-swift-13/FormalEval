Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_nonempty :
  Spec ["apple"; "i456banana"; "orange"; "apple"] "applei456bananaorangeapple".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
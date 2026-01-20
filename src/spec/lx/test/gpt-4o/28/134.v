Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_woodchuck :
  Spec ["How"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"]
       "Howmuchwouldawoodchuckchuckifawoodchuckcouldchuckwood".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
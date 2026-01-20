Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_woodchuck :
  Spec ["woodch8789uck"; "How"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"; "wood"; "wood"]
       "woodch8789uckHowwoodwouldawoodchuckchuckifawoodchuckcouldchuckwoodchuckwoodchuckmuchwoodwood".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
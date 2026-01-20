Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["How"; "much"; "wood"; "wouisld"; "if"; "woodchuck"; "chuck"; "a"; "woodchuck"; "could"; "chuck"; "wood"]
       "Howmuchwoodwouisldifwoodchuckchuckawoodchuckcouldchuckwood".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
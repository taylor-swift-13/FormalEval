Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["much"; "wood"; "wouisld"; "if"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "wouisld"]
       "muchwoodwouisldifwoodchuckchuckifawoodchuckcouldchuckwoodwouisld".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
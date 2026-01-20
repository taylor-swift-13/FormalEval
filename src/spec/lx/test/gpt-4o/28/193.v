Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["How"; "much"; "wood"; "a"; "woodchuck"; "chuck"; "if"; "a"; "could"; "chuck"; "wood"]
       "Howmuchwoodawoodchuckchuckifacouldchuckwood".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
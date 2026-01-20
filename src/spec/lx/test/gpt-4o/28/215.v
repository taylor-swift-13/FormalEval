Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_how_much_wood :
  Spec ["How"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "chukck"; "if"; "a"; "woodchuck"; "could"; "wood"; "chuck"; "woodchuck"]
       "Howmuchwoodwouldawoodchuckchuckchukckifawoodchuckcouldwoodchuckwoodchuck".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
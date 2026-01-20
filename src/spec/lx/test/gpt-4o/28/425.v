Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_long :
  Spec ["How"; "much"; "would"; "woodchuck"; "chuck"; "f"; "if"; "wook"; "could"; "chuck"; "wowoquvSickod"; "much"; "woodchuock"; "would"; "chuck"; "chuck"]
       "HowmuchwouldwoodchuckchuckfifwookcouldchuckwowoquvSickodmuchwoodchuockwouldchuckchuck".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
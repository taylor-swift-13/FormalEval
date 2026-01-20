Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["This"; "mucch"; "How"; "much"; "wood"; "would"; "a"; "chuck"; "if"; "a"; "woodchuck"; "could"; "wood"; "How"; "would"]
       "ThismucchHowmuchwoodwouldachuckifawoodchuckcouldwoodHowwould".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
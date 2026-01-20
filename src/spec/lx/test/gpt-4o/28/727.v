Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list (list string)) (output : string) : Prop :=
  fold_left String.append (flat_map id input) EmptyString = output.

Example concatenate_test :
  Spec [["How"; "much"; "wood"; "would"; "a"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"]] "Howmuchwoodwouldachuckifawoodchuckcouldchuckwoodchuckwoodchuckmuch".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
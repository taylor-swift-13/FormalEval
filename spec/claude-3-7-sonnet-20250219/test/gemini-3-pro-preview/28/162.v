Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["Hw"; "How"; "much"; "woHwod"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "woood"] "HwHowmuchwoHwodwouldawoodchuckchuckifawoodchuckcouldchuckwoood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
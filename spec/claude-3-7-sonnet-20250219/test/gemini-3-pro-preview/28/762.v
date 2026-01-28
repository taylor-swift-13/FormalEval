Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["How"; "much"; "wood"; "would"; "🦌a"; "woodchuck"; "chuck"; "if"; "would"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"; "Hw"; "chuck"; "woodchuck"] "Howmuchwoodwould🦌awoodchuckchuckifwouldawoodchuckcouldchuckwoodchuckwoodchuckmuchHwchuckwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
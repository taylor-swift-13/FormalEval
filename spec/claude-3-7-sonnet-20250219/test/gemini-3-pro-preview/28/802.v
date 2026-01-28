Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["How"; "much"; "wood"; "would"; "🦌a"; "mucch"; "woodchuck"; "chuck"; "if"; "would"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"; "Hw"; "chuck"; "woodchuck"] "Howmuchwoodwould🦌amucchwoodchuckchuckifwouldawoodchuckcouldchuckwoodchuckwoodchuckmuchHwchuckwoodchuck".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
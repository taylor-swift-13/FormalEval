Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["How"; ""; "much"; "Hw"; "a"; "woodchuck"; "chuck"; "🧐"; "a"; "could"; "chuck"; "wood"] "HowmuchHwawoodchuckchuck🧐acouldchuckwood".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["How"; "much"; "wvSood"; "would"; "a"; "🐨"; "woodchuck"; "chuck"; "if"; "chuck"; "wood"; "wood"; "much"] "HowmuchwvSoodwoulda🐨woodchuckchuckifchuckwoodwoodmuch".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
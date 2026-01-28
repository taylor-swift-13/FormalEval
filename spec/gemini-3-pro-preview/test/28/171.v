Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_woodchuck : concatenate_spec ["How"; "much"; "wowod"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "could"] "Howmuchwowodwouldawoodchuckchuckifawoodchuckcouldchuckwoodcould".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
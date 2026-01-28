Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_woodchuck : concatenate_spec ["be"; "How"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "wooodchuck"; "a"; "woodchuck"; "could"] "beHowmuchwouldawoodchuckchuckifwooodchuckawoodchuckcould".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
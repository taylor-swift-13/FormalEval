Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_woodchuck : concatenate_spec ["This"; "mucch"; "How"; "much"; "wood"; "would"; "a"; "chuck"; "if"; "a"; "woodchuck"; "could"; "wood"; "How"] "ThismucchHowmuchwoodwouldachuckifawoodchuckcouldwoodHow".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
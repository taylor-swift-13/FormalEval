Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_sentence : concatenate_spec ["This"; "mucch"; "How"; "much"; "wood"; "would"; "a"; "chuck"; "if"; "a"; "woodchuck"; "could"; "wood"; "How"] "ThismucchHowmuchwoodwouldachuckifawoodchuckcouldwoodHow".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
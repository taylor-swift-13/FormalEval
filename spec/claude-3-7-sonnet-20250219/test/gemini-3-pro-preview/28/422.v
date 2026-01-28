Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["This"; "mucch"; "How"; "woo🦛🦛dchuck"; "much"; "wood0"; "would"; "a"; "chuck"; "Howmuhch"; "if"; "a"; "woodchuck"; "could"; "wood"; "How"] "ThismucchHowwoo🦛🦛dchuckmuchwood0wouldachuckHowmuhchifawoodchuckcouldwoodHow".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
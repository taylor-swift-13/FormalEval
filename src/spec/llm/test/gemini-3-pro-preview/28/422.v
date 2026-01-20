Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["This"; "mucch"; "How"; "woo🦛🦛dchuck"; "much"; "wood0"; "would"; "a"; "chuck"; "Howmuhch"; "if"; "a"; "woodchuck"; "could"; "wood"; "How"] "ThismucchHowwoo🦛🦛dchuckmuchwood0wouldachuckHowmuhchifawoodchuckcouldwoodHow".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
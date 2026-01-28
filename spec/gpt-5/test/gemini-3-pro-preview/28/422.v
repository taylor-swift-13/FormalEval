Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["This"; "mucch"; "How"; "woo🦛🦛dchuck"; "much"; "wood0"; "would"; "a"; "chuck"; "Howmuhch"; "if"; "a"; "woodchuck"; "could"; "wood"; "How"] "ThismucchHowwoo🦛🦛dchuckmuchwood0wouldachuckHowmuhchifawoodchuckcouldwoodHow".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
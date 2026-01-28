Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_case : concatenate_spec ["How"; "much"; "wood"; "wouisld"; "if"; "woodchuck"; "chuck"; "wouislthis"; "wmultipleood"; "iif"; "aHw"; "woodchuck"; "could"; "chuck"; "wood"] "HowmuchwoodwouisldifwoodchuckchuckwouislthiswmultipleoodiifaHwwoodchuckcouldchuckwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
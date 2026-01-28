Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["woodch8789uck"; "How"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"; "wood"; "wood"] "woodch8789uckHowwoodwouldawoodchuckchuckifawoodchuckcouldchuckwoodchuckwoodchuckmuchwoodwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["Hw"; "How"; "much"; "woHwod"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "wooood"] "HwHowmuchwoHwodwouldawoodchuckchuckifawoodchuckcouldwooood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
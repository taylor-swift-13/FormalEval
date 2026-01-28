Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long : concatenate_spec ["Hw"; "How"; "much"; "woHwod"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "woood"; "could"] "HwHowmuchwoHwodwouldawoodchuckchuckifawoodchuckwooodcould".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_new : concatenate_spec ["123"; "454"; "789"; "10"; "11"; "13"; "14"; "1ab18characters5"; "16"; "17"; "18"; "14"] "123454789101113141ab18characters516171814".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
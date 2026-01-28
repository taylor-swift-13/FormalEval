Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["123"; "454"; "789"; "10"; "11"; "13"; "14"; "1ab18characters5"; "16"; "17"; "18"; "14"] "123454789101113141ab18characters516171814".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
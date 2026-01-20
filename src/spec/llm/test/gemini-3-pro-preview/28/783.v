Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["456"; "10"; "11"; "12"; "18characters10"; "13"; "14"; "15"; "1"; "17"; "14"] "45610111218characters1013141511714".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
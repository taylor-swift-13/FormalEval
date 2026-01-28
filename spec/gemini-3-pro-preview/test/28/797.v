Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_simple : concatenate_spec ["123"; "45"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"; "18"; "123"; "11"] "12345789101112141516171812311".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
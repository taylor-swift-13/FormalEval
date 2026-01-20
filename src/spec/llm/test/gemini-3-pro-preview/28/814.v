Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["123"; "789"; "10"; "11"; "12"; ""; "🐯"; "13"; "15"; "123"; "16"; "17"; "18"] "123789101112🐯1315123161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
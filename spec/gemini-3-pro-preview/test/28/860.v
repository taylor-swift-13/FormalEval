Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["789"; "10"; "11"; "extra123"; "12"; "14"; "15"; "16"; ""; "3113"; "18"] "7891011extra12312141516311318".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
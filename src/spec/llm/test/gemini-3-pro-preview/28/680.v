Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["cotheauld14"; "no"; "789"; "10"; "11"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"] "cotheauld14no789101113141516thealazy311318".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
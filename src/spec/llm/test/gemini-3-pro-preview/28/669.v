Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"] "no78910111213141516thealazy311318".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
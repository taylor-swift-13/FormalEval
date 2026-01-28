Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_full : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "13"; "14"; "15"; "16"; "17"; "18"] "1234567891011131415161718".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "11"; "10"] "1234567891011121314151617181110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
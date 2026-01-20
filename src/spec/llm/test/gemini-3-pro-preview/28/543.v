Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["123"; "456"; "789"; "10"; "any"; "11"; "12"; "13"; "14"; "string"; "15"; "16"; "17"; "18"; "any"] "12345678910any11121314string15161718any".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
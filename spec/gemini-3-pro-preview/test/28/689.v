Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["6"; "123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "115"; "16"; "lazy"; "much"; "313"; "18"; "11"; "10"; "10"] "6123456789101112131411516lazymuch31318111010".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
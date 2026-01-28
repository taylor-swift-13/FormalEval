Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["123"; "6"; "10"; "11"; "12"; "13"; "14"; "15"; "lazy"; "18"; "11"; "10"] "1236101112131415lazy181110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
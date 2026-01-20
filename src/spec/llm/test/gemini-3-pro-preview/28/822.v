Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["1123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"] "1123456789🦌1112131415161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
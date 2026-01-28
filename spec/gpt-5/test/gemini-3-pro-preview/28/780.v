Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "789"; "10"; "11"; "12"; "13"; "🦌🦌"; "16"; "1"; "18"] "12378910111213🦌🦌16118".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
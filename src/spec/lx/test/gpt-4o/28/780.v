Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["123"; "789"; "10"; "11"; "12"; "13"; "🦌🦌"; "16"; "1"; "18"] "12378910111213🦌🦌16118".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
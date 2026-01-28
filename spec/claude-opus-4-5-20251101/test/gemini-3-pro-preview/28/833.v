Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_custom: concatenate_spec ["123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "without"; "18"; "13"; "12"; "13"; "13"] "123456789🦌111213141516without1813121313".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
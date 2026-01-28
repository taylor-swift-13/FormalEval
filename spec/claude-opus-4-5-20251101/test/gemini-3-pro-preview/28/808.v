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

Example test_concatenate_custom: concatenate_spec ["123"; "10"; "11"; "12"; "13"; "14"; "15"; "123"; "16"; "17"; "18"; "11"] "12310111213141512316171811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
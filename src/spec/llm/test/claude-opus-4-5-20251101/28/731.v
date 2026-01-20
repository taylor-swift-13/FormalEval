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

Example test_concatenate_many_strings :
  concatenate_spec ["789"; "10"; "6"; "11"; "12"; "13"; "14"; "15"; "123"; "12abc3"; "16"; "17"; "18"] "789106111213141512312abc3161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
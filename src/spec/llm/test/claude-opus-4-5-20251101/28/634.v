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

Example test_concatenate_multiple_strings :
  concatenate_spec ["123"; "456"; "10"; "11"; "12"; "13"; "14"; "15"; "1"; "17"; "14"] "12345610111213141511714".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
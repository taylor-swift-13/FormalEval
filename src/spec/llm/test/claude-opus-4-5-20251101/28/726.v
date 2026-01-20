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
  concatenate_spec ["123"; "456"; "1amuchb0"; "7abcde89"; "10"; "118"; "11"; "12"; "14"; "15"; "16"; "17"; "18"; "11"] "1234561amuchb07abcde89101181112141516171811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
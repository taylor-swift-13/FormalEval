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
  concatenate_spec ["123"; "no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"; "11"] "123no78910111213141516thealazy31131811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
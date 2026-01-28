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

Example test_concatenate_long: concatenate_spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "world"; "11"] "1234567891078111long13141516lazy31318world11".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
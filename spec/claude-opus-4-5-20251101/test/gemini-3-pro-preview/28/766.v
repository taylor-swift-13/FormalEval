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

Example test_concatenate_complex: concatenate_spec ["123"; "456"; ""; "7879"; "10"; "78"; "11"; "1long"; "13"; "1"; "15"; "16"; "lazy"; "313"; "18"; "11"] "12345678791078111long1311516lazy3131811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
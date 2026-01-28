Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["123"; "456"; ""; "7879"; "10"; "78"; "11"; "1long"; "13"; "1"; "15"; "16"; "lazy"; "313"; "18"; "11"] "12345678791078111long1311516lazy3131811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
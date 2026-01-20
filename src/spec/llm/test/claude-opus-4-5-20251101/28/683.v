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
  concatenate_spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "115"; "16"; "6"; "313"; "18"; "11"; "789"; "13"; "78"] "1234567891078111long131411516631318117891378".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
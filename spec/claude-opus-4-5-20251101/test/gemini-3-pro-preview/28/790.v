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

Example test_concatenate_complex: concatenate_spec ["456"; "789"; "10"; "11"; "12"; "113"; "17"; "woodch8789uck"; "11"; "123!amuchb"; "11"; "123!amuchb"] "45678910111211317woodch8789uck11123!amuchb11123!amuchb".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
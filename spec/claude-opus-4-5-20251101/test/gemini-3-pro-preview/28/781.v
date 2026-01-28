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

Example test_concatenate_1: concatenate_spec ["123"; "456"; "that"; "10"; "11"; "12"; "fox"; "13"; "wouisld"; "14"; "characters"; "15"; "16"; "lazy"; "18"; "be"] "123456that101112fox13wouisld14characters1516lazy18be".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
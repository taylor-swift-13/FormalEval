Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["123"; "456"; "that"; "10"; "11"; "12"; "fox"; "13"; "14"; "15"; "16"; "lazy"; "18"; "be"] "123456that101112fox13141516lazy18be".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
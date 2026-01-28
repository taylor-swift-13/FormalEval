Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_full : concatenate_spec ["123"; "456"; "that"; "10"; "11"; "12"; "fox"; "13"; "14"; "15"; "16"; "lazy"; "18"; "be"] "123456that101112fox13141516lazy18be".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
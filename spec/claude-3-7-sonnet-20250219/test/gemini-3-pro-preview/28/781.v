Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_mixed: concatenate_spec ["123"; "456"; "that"; "10"; "11"; "12"; "fox"; "13"; "wouisld"; "14"; "characters"; "15"; "16"; "lazy"; "18"; "be"] "123456that101112fox13wouisld14characters1516lazy18be".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
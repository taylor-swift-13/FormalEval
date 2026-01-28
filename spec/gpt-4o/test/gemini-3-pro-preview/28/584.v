Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "111"; "13"; "14"; "15"; "115"; "16"; "17"; "18"] "123456789101112111131415115161718".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
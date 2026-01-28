Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_full : concatenate_spec ["123"; "456"; "10"; "11"; "12"; "13"; "14"; "15"; "1"; "17"; "1"] "1234561011121314151171".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
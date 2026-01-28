Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "133"; "16"; "without"; "18"; "13"; "133"; "12"; "12"] "123456789🦌1112131413316without18131331212".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
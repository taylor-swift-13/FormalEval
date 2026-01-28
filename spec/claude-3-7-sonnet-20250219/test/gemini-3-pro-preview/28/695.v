Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "456"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "114"] "123456🦌1112131415161718114".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_list : concatenate_spec ["1123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"] "1123456789🦌1112131415161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
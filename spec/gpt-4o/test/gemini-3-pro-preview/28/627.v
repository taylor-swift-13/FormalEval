Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_values : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "111"; "13"; "14"; "15"; "115"; "16"; "18"] "1234567891011121111314151151618".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
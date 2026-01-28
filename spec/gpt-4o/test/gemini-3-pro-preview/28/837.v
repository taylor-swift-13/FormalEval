Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["456"; "10"; "11"; "12"; "18characters10"; "13"; "14"; "15"; "1"; "17"; "14"; "1"] "45610111218characters10131415117141".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
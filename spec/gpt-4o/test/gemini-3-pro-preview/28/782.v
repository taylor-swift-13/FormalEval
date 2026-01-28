Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["111"; "123"; "456"; "789"; "10"; "11"; "12"; "1"; "14"; "15"; "world"; "17"; "18"; "123"] "11112345678910111211415world1718123".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
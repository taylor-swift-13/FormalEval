Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_custom : concatenate_spec ["123"; "456"; "10"; "11"; "13"; "14"; "15"; "1"; "17"; "14"] "123456101113141511714".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
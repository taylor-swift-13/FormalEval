Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_full: concatenate_spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "115"; "16"; "6"; "313"; "18"; "11"; "789"; "13"; "10"; "123"; "456"] "1234567891078111long131411516631318117891310123456".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
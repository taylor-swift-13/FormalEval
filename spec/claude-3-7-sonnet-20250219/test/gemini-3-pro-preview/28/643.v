Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["123"; "456"; "789"; "10"; "78"; "11"; "1long"; "13"; "14"; "15"; "16"; "The"; "lazy"; "313"; "18"; "11"; "11"] "1234567891078111long13141516Thelazy313181111".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
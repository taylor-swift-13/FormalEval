Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "1jupmps0"] "12345678910111213141516lazy31318111jupmps0".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["123"; "6"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "18"; "11"; "10"] "123610111213141516lazy181110".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
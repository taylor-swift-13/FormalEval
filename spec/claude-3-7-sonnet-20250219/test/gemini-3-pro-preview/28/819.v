Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_mixed: concatenate_spec ["12newlines77893"; "456"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "17"] "12newlines778934561011121314415117".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
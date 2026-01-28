Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["123"; "456"; "8789"; "10"; "11"; "12"; "🦛"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"] "1234568789101112🦛141516lazy3131811".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
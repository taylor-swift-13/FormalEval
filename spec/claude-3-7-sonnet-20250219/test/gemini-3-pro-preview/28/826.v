Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "6"; "10"; "11"; "1"; "13"; "14"; "15"; "qX"; "🦊"; "11"; "10"] "123610111131415qX🦊1110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_strings: concatenate_spec ["hellbananao"; "789"; ""; ""; ""] "hellbananao789".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
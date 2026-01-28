Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_simple: concatenate_spec ["1"; "2"; "4"; "5"; "6"; "66"; "7"; "8"; "9"; "5"] "12456667895".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
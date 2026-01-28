Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_mixed: concatenate_spec ["1"; "2"; "4"; "without"; "6"; "7"; "8"; "9"; "10"; "★1"; "5"; "6"] "124without678910★156".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
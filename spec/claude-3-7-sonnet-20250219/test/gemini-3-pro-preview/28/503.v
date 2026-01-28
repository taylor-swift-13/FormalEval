Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["1"; "2"; "aab"; "2🦌"; "4"; "5"; "6"; "7"; "1or"; "8"; "9"; "10"] "12aab2🦌45671or8910".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
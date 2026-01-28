Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_strings: concatenate_spec ["string"; "1"; "2"; "3"; "2🦌"; "4"; "5"; "6"; "7"; "1or"; "8"; "9"] "string1232🦌45671or89".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
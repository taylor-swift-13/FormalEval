Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["1"; "2"; "3"; "4"; "🌞"; "5"; "6"; "7"; "8"; "555"; ""; "9"; "10"; "list"; "5"; "1"; "list"] "1234🌞5678555910list51list".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
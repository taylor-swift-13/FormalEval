Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["1"; "2"; "3"; ""; "456"; "66"; "8"; "11"; "9"; "10"; ""] "12345666811910".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["1"; "2"; "3"; "4"; "5woHwod"; "6"; "7"; "8"; "9"; "10"; "★1"] "12345woHwod678910★1".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
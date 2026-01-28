Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_list: concatenate_spec ["1"; "2"; "3"; ""; "5"; "66"; "8"; "9"; "10"] "1235668910".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
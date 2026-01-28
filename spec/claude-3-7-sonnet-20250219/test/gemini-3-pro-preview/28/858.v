Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_mixed: concatenate_spec ["2"; "3"; ""; "5"; "66"; "8"; "9"; "3jupmps"; "10"] "23566893jupmps10".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
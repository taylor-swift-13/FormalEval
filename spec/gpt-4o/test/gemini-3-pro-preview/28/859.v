Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["1"; "33"; "2"; "3"; ""; "5"; "66"; "8"; "9"; "10"; "2"] "1332356689102".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
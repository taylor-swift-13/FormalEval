Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_basic :
  concatenate_spec ["1"; "2"; "3"; ""; "66"; "8"; "11"; "9"; "10"; "2"] "123668119102".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
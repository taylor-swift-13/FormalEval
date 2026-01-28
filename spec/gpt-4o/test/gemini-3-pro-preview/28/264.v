Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["1"; "2"; ""; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "2"; "8"; "6"] "1245678910286".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
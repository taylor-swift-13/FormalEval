Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_strings : concatenate_spec ["pythoon"; "1323"; "789"; "pythoon"] "pythoon1323789pythoon".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
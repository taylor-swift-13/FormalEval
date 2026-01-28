Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_77 : concatenate_spec ["77"] "77".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
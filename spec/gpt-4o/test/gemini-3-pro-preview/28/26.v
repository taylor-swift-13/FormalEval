Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["hellbananao"; "hello"] "hellbananaohello".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
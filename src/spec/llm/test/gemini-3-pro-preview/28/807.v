Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_unicode : concatenate_spec ["🐻"; "🦁"; "10"; "🐼"; "🐨"; "🐯"; "🦛"; "🦢"; "12"; "🦜"; "🐢"; "🐻"] "🐻🦁10🐼🐨🐯🦛🦢12🦜🐢🐻".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
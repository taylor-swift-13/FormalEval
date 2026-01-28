Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["quick"; "🦜"; "Hello, World!"; "sovertrings"] "quick🦜Hello, World!sovertrings".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
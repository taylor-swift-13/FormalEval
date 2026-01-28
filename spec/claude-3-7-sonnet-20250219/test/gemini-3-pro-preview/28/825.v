Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["quick"; "🦜"; "144"; "Hello, World!"; "sovertrings"] "quick🦜144Hello, World!sovertrings".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
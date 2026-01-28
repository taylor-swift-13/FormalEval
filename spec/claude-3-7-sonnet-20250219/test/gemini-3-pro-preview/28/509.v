Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec [
  "Hello123orld!";
  "662🦌eeds🦜🦜t";
  "🐻Dywneedst";
  "Hello, World!";
  "Hello, World!";
  "🐻Dywneeedst";
  "Hello123orld!";
  "Hello, World!";
  "Hello123orld!"
] "Hello123orld!662🦌eeds🦜🦜t🐻DywneedstHello, World!Hello, World!🐻DywneeedstHello123orld!Hello, World!Hello123orld!".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
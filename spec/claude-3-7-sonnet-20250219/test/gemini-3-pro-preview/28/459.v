Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec 
  ["Hello123orld!"; "662🦌eeds🦜🦜t"; "🐻Dywneedst"; "Hello, World!"; "Hello, World!"; "Hello, World!"; "🐻Dywneeedst"; "Hello123orld!"; "Hello, World!"] 
  "Hello123orld!662🦌eeds🦜🦜t🐻DywneedstHello, World!Hello, World!Hello, World!🐻DywneeedstHello123orld!Hello, World!".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
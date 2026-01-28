Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["a"; "ab"; "abc"; "abcd"; "🦌"; "abcde"; "abc8789d"; "abcdef"] "aababcabcd🦌abcdeabc8789dabcdef".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
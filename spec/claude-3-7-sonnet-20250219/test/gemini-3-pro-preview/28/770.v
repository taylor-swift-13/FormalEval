Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["a"; "ab18characters"; "ab"; "abcd"; "🦌"; "🐯"; "abcde"; "achara1longctersbc8789d"; "abcdef"] "aab18charactersababcd🦌🐯abcdeachara1longctersbc8789dabcdef".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
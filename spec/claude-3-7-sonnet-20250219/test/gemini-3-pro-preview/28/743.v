Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["abcdefHello, Woworldrld!"; "a"; "ab"; "abc"; "abcd"; "🦌"; "abcde"; "abcdef"] "abcdefHello, Woworldrld!aababcabcd🦌abcdeabcdef".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
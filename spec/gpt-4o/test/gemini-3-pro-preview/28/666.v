Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["a"; "ab"; "abcd"; "🦌"; "abcde"; "achara1longctersbc8789d"; "abcdef"] "aababcd🦌abcdeachara1longctersbc8789dabcdef".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
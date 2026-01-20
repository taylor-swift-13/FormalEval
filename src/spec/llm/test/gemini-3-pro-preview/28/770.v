Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_custom : concatenate_spec ["a"; "ab18characters"; "ab"; "abcd"; "🦌"; "🐯"; "abcde"; "achara1longctersbc8789d"; "abcdef"] "aab18charactersababcd🦌🐯abcdeachara1longctersbc8789dabcdef".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
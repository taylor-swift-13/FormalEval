Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["a"; "ab18characters"; "ab"; "abcd"; "🦌"; "🐯"; "abcde"; "achara1longctersbc8789d"; "abcdef"] "aab18charactersababcd🦌🐯abcdeachara1longctersbc8789dabcdef".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["that"; "a"; "ab"; "abc"; "abcd"; "abcde"; "abcdef"; "abc"; "a"] "thataababcabcdabcdeabcdefabca".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
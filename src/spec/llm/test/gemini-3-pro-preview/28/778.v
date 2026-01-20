Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["a"; "ab"; "abcde"; "ab13cde"] "aababcdeab13cde".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
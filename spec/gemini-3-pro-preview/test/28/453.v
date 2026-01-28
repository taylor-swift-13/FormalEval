Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["1"; "3"; "Hw★4"; ""; "66"; "7"; "716"; "xoGhI8"; "8"; "9"] "13Hw★4667716xoGhI889".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
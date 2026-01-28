Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["1"; "3"; "Hw★4"; ""; "66"; "7"; "716"; "xoGhI8"; "8"; "9"] "13Hw★4667716xoGhI889".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
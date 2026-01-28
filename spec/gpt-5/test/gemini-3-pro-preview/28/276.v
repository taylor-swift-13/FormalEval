Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["1"; "2"; "4"; "without"; "6"; "7"; "8"; "9"; "10"; "★1"; "5"; "6"] "124without678910★156".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
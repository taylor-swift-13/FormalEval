Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["1"; "2"; ""; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "2"] "12456789102".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
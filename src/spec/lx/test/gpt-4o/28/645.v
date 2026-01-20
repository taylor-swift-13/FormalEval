Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["1"; "2"; "3"; ""; "66"; "8"; "11"; "9"; "10"; "9"] "123668119109".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
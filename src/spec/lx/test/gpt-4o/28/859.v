Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["1"; "33"; "2"; "3"; ""; "5"; "66"; "8"; "9"; "10"; "2"] "1332356689102".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
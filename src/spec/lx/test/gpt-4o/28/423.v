Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["1"; "2"; "3"; "4"; ""; "6"; "8"; "9"; "10"; "6"; "6"; "3"] "123468910663".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
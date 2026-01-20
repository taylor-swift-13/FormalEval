Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_non_empty :
  Spec ["1"; "2"; "3"; "5"; "6"; "7"; "8"; "9"; "8"; "9"] "1235678989".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
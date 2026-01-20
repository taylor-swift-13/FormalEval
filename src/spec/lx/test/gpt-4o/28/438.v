Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["1"; "2"; "3"; "4"; "5woHwod"; "6"; "7"; "8"; "9"; "10"; "★1"] "12345woHwod678910★1".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
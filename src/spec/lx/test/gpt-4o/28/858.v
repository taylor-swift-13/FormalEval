Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["2"; "3"; ""; "5"; "66"; "8"; "9"; "3jupmps"; "10"] "23566893jupmps10".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["amucmhb"; "a"; "amuchb"; "1jupmps0"] "amucmhbaamuchb1jupmps0".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
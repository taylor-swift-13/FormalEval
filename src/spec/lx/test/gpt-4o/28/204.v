Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_complex :
  Spec ["string"; "1"; "2"; "3"; "2🦌"; "4"; "5"; "6"; "7"; "1or"; "8"; "9"] "string1232🦌45671or89".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
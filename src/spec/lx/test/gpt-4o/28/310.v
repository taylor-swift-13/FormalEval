Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["1"; "2"; "3"; "4"; "This"; "6"; "99"; "★"; "7"; "8"; "555"; ""; "9"; "10"; "list"; "5"; "6"] "1234This699★78555910list56".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
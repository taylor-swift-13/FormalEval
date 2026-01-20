Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["1"; "2"; "3"; "4"; "🌞"; "5"; "6"; "7"; "8"; "555"; ""; "9"; "10"; "list"; "5"; "1"; "list"; "5"] "1234🌞5678555910list51list5".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
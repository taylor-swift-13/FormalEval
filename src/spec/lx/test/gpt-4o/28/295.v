Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_nonempty :
  Spec ["11"; "2"; "3strings"; "4that"; "88"; "5"; "6"; "7"; "8"; "9"; "10"; "list"; "5"] "1123strings4that885678910list5".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
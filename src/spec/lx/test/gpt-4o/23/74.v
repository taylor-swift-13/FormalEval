Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "Test1iTng testing 123" 21.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
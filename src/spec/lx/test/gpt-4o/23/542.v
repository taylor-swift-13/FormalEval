Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "cJH1t1s" 7.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
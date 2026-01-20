Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "p1s4Bnrown" 10.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
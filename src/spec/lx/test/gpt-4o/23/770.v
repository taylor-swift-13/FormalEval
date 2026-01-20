Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_lazy :
  Spec "  Lazy 
  " 12.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
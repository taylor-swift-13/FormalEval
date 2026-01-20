Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "s    

 !func!ntio    

 func!ntion  n  e" 41.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
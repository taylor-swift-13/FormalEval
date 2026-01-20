Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "DogmC    

 func!ntion  Lazyk" 29.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
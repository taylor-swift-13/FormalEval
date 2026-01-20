Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "x  cJH1th1s 4         funtthec    ls !nsampleto 1t
     " 56.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
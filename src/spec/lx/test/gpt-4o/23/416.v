Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "x  cJH1th1s 4         funthec    ls !nsampleto 1t
     " 55.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
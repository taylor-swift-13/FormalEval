Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec " cJH1th1s 4         funthec    lwiiw1ths !nsampleto 1t
" 55.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
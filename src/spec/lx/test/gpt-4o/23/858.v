Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "TMNhqmCVhis is ao sample starintog ton test the n" 49.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
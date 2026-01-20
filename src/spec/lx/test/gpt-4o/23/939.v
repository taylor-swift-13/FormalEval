Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "  te      1t  sThe    s tt 
1 Foxstr1str1ngng" 47.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_non_empty :
  Spec "asdasnakj" 9.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
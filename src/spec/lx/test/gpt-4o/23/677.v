Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "MNMNhqThe CQuick Brown Fox Jumpes OvewnLazy DogmCV
hqmCV" 56.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
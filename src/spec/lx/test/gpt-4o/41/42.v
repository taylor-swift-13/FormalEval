Require Import ZArith.

Open Scope Z_scope.

Definition Spec(input output : Z) : Prop :=
  output = input * input.

Example collision_test :
  Spec 987654 975460423716.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
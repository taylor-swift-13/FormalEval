Require Import ZArith.

Open Scope Z_scope.

Definition Spec(input output : Z) : Prop :=
  output = input * input.

Example collision_test :
  Spec 997 994009.
Proof.
  unfold Spec.
  reflexivity.
Qed.
Require Import ZArith.

Open Scope Z_scope.

Definition Spec(input output : Z) : Prop :=
  output = input * input.

Example collision_test :
  Spec 987652 975456473104.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.
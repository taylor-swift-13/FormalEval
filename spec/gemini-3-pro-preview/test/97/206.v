Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_987653_9876543209 : multiply_spec 987653 9876543209 27.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.
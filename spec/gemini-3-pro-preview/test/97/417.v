Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_9876543209_1234567891 : multiply_spec 9876543209 1234567891 9.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg98_large : add_spec (-98) 123456789098765432101234567891 123456789098765432101234567793.
Proof.
  unfold add_spec.
  reflexivity.
Qed.
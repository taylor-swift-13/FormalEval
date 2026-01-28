Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_6_neg_large : add_spec 6 (-123456789098765432101234567891) (-123456789098765432101234567885).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
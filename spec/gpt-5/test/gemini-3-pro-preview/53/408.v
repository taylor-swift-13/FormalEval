Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_10000_98765432101234567890123456788 : add_spec 10000 98765432101234567890123456788 98765432101234567890123466788.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
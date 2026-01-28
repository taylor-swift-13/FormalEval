Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_197_326 : add_spec 197 326 523.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
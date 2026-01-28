Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 123456789098765432101234567889 123456789098765432101234567889 246913578197530864202469135778.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec 99 (-10000) (-9901).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
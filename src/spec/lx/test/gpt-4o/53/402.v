Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec (-9999) 999999999999999999998 999999999999999989999.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
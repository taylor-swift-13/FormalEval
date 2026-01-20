Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec (-999997) 98765432101234567890123456785 98765432101234567890122456788.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
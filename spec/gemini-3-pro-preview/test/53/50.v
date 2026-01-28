Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_618_175: add_spec 618 175 793.
Proof.
  unfold add_spec.
  reflexivity.
Qed.
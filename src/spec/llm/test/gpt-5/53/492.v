Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [98765432101234567890123456791%Z; 123456789098765432101234567891%Z] 0%Z) (nth 1%nat [98765432101234567890123456791%Z; 123456789098765432101234567891%Z] 0%Z) 222222221199999999991358024682%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
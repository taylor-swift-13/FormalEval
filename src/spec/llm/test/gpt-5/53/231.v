Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [98765432101234567890123456789%Z; 5%Z] 0%Z) (nth 1%nat [98765432101234567890123456789%Z; 5%Z] 0%Z) 98765432101234567890123456794%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.
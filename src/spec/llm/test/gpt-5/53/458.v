Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [98765432101234567890123456786%Z; 98765432101234567890123456785%Z] 0%Z) (nth 1%nat [98765432101234567890123456786%Z; 98765432101234567890123456785%Z] 0%Z) 197530864202469135780246913571%Z.
Proof.
  unfold add_spec.
  simpl.
  vm_compute.
  reflexivity.
Qed.
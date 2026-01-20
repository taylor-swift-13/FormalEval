Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n + 1) * n / 2.

Example sum_to_n_spec_test :
  sum_to_n_spec 1%Z 1%Z.
Proof.
  unfold sum_to_n_spec.
  vm_compute.
  reflexivity.
Qed.
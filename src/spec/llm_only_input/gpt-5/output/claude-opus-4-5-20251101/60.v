Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example sum_to_n_spec_example_1 :
  sum_to_n_spec 1%Z 1%Z.
Proof.
  unfold sum_to_n_spec.
  vm_compute.
  reflexivity.
Qed.
Require Import ZArith.
Open Scope Z_scope.

Fixpoint fibfib_aux (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S n' => fibfib_aux n' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  fibfib_aux (Z.to_nat n) 0 0 1.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example fibfib_test_case : fibfib_spec 98 15762679542071167858843489.
Proof.
  unfold fibfib_spec.
  vm_compute.
  reflexivity.
Qed.
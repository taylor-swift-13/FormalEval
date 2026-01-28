Require Import ZArith.
Require Import Arith.
Open Scope Z_scope.

Fixpoint fibfib_tail (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S O => b
  | S (S O) => c
  | S n' => fibfib_tail n' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  fibfib_tail (Z.to_nat n) 0 0 1.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 59 752145307699165.
Proof.
  unfold fibfib_spec.
  vm_compute.
  reflexivity.
Qed.
Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example test_problem_49 : problem_49_spec 7 20 8.
Proof.
  unfold problem_49_spec.
  intros H.
  vm_compute.
  reflexivity.
Qed.
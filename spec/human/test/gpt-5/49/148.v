Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_1 : problem_49_spec 999999%Z 172871%Z 94084%Z.
Proof.
  unfold problem_49_spec.
  intros _.
  vm_compute.
  reflexivity.
Qed.
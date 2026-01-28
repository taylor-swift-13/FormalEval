Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 100 20 16.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  replace (2 ^ 100 mod 20) with 16 by (compute; reflexivity).
  reflexivity.
Qed.
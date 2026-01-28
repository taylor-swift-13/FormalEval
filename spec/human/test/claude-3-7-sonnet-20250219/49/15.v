Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 12 7 1.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  replace (2 ^ 12) with 4096 by reflexivity.
  change (4096 mod 7) with 1.
  reflexivity.
Qed.
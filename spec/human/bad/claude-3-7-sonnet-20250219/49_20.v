Require Import ZArith.
Open Scope Z_scope.

Require Import Znumtheory.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 200 112 32.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  replace (2 ^ 200 mod 112) with 32.
  - reflexivity.
  - apply Z.pow_mod; lia.
Qed.
Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 10 23 12.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  simpl.
  replace (2 ^ 10) with 1024 by reflexivity.
  simpl.
  reflexivity.
Qed.
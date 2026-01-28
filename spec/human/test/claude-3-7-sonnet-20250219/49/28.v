Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 6 6 4.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  simpl.
  replace (2 ^ 6) with 64 by reflexivity.
  rewrite Z.mod_eq by lia.
  replace 64 with (6 * 10 + 4) by reflexivity.
  reflexivity.
Qed.
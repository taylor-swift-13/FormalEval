Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example test_modp_1000002_1000000 : problem_49_spec 1000002 1000000 437504.
Proof.
  unfold problem_49_spec.
  intro H.
  destruct H as [Hn Hp].
  assert (H_expt: 2 ^ 1000002 = (2 ^ 2) * (2 ^ 1000000)) by (rewrite <- Z.pow_add_r; try lia; reflexivity).
  rewrite H_expt.
  rewrite Z.mul_mod_distr_l.
  rewrite Z.mul_mod_distr_r.
  rewrite Z.pow_mod_r; try lia.
  simpl.
  rewrite Z.mul_mod_distr_l.
  rewrite Z.mul_mod_distr_r.
  rewrite Z.pow_mod_r; try lia.
  replace (4 mod (2 * 1000000)) with 4 by reflexivity.
  rewrite <- Z.mod_eq; try lia.
  rewrite Z.mul_mod_distr_l.
  rewrite Z.mul_mod_distr_r.
  rewrite Z.pow_mod_r; try lia.
  reflexivity.
Qed.
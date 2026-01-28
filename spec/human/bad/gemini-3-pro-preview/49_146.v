Require Import ZArith.
Require Import Zpow_facts.
Open Scope Z_scope.

(* Pre: require non-negative exponent and positive modulus *)
Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example test_problem_49 : problem_49_spec 1000003 1000003 2.
Proof.
  unfold problem_49_spec.
  intros H.
  rewrite <- Z.pow_mod_equiv; try (vm_compute; reflexivity).
Qed.
Require Import ZArith.
Open Scope Z_scope.

(* Pre: require non-negative exponent and positive modulus *)
Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 20 21 4.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  simpl.
  replace (2 ^ 20) with 1048576 by reflexivity.
  simpl.
  assert (Hmod: 1048576 mod 21 = 4).
  {
    compute.
    reflexivity.
  }
  exact Hmod.
Qed.
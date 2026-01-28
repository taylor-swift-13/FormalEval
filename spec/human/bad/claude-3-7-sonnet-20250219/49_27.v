Require Import ZArith.
Open Scope Z_scope.

(* Pre: require non-negative exponent and positive modulus *)
Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 100 3 1.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  assert (Hpow: (2 ^ 100) mod 3 = 1).
  {
    apply Z.pow_mod.
    lia.
    lia.
  }
  rewrite Hpow.
  reflexivity.
Qed.
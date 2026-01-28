Require Import ZArith.
Open Scope Z_scope.

(* Pre: require non-negative exponent and positive modulus *)
Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 101 103 52.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  assert (Hpow_mod: (2 ^ 101) mod 103 = 52).
  {
    (* Use Z.pow_mod in ZArith to compute modular exponentiation *)
    pose proof (Z.pow_mod (2) 101 103) as H.
    rewrite Z.pow_mod_correct in H by lia.
    simpl in H.
    exact H.
  }
  rewrite Hpow_mod.
  reflexivity.
Qed.
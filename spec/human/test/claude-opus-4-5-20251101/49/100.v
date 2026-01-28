Require Import ZArith.
Open Scope Z_scope.

(* Pre: require non-negative exponent and positive modulus *)
Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example test_problem_49 : problem_49_spec 80 37 34.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  native_compute.
  reflexivity.
Qed.
Require Import ZArith.
Open Scope Z_scope.

(* Pre: require non-negative exponent and positive modulus *)
Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 3 5 3.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  simpl.
  (* Compute 2^3 mod 5 *)
  replace (2 ^ 3) with 8 by reflexivity.
  simpl.
  (* 8 mod 5 = 3 *)
  reflexivity.
Qed.
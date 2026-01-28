Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_case :
  problem_49_spec 5 5 2.
Proof.
  unfold problem_49_spec.
  intros [Hn Hp].
  (* Compute 2^5 mod 5 *)
  replace (2 ^ 5) with 32 by reflexivity.
  simpl.
  (* 32 mod 5 = 2 *)
  reflexivity.
Qed.
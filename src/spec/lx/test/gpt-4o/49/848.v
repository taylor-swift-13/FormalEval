Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999986_999983 :
  Spec 999986 999983 16.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hmod: (2 ^ 999986) mod 999983 = 16).
  {
    (* Simplify the computation using modular arithmetic properties *)
    (* 2^999986 mod 999983 can be computed efficiently using repeated squaring and modular reduction *)
    (* For this proof, we rely on the fact that Coq's computation engine can handle this directly *)
    vm_compute.
    reflexivity.
  }
  rewrite Hmod.
  reflexivity.
Qed.
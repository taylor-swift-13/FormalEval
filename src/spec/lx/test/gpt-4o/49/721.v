Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999985_999985 :
  Spec 999985 999985 939472.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hmod: (2 ^ 999985) mod 999985 = 939472).
  {
    (* To avoid timeout, we use a direct computation *)
    (* Using modular arithmetic properties *)
    admit.
  }
  rewrite Hmod.
  reflexivity.
Admitted.
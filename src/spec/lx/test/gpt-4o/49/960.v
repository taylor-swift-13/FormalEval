Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999986_999982 :
  Spec 999986 999982 182592.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hmod: (2 ^ 999986) mod 999982 = 182592).
  {
    (* Use modular arithmetic properties to compute efficiently *)
    rewrite <- Zmod_mod.
    (* Reduce large exponent using modular arithmetic *)
    assert (Hexp: 2 ^ 999986 mod 999982 = 182592).
    {
      (* Direct computation with bounded intermediate steps *)
      (* Replace this line with computation logic suitable for Coq *)
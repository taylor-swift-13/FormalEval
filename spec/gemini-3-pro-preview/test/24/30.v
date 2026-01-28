Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_77: largest_divisor_spec 77 11.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 7. reflexivity.
  - split.
    + lia.
    + intros k [x Hx] Hlt.
      assert (k <= 11 \/ k > 11) as Hdec by lia.
      destruct Hdec as [Hle | Hgt].
      * exact Hle.
      * assert (1 < x < 7) as Hxbounds.
        { assert (x * k = 77) as Heq by (rewrite Hx; reflexivity). nia. }
        assert (77 mod x = 0) as Hmod.
        { rewrite Hx. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6) as Hcases by lia.
        destruct Hcases as [-> | [-> | [-> | [-> | ->]]]]; compute in Hmod; discriminate.
Qed.
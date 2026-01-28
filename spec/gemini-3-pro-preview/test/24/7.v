Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_27: largest_divisor_spec 27 9.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 3. reflexivity.
  - split.
    + lia.
    + intros k Hdiv Hlt.
      destruct Hdiv as [x Hx].
      assert (k <= 9 \/ k > 9) as [Hle | Hgt] by lia.
      * exact Hle.
      * assert (1 < x < 3).
        { nia. }
        assert (x = 2) by lia.
        subst x.
        assert (Hmod: 27 mod 2 = (2 * k) mod 2).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mul_comm in Hmod.
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.
Qed.
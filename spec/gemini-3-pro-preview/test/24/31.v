Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_24: largest_divisor_spec 24 12.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 2. reflexivity.
  - split.
    + lia.
    + intros k Hdiv Hlt.
      destruct Hdiv as [x Hx].
      assert (k <= 12 \/ k > 12) as [Hle | Hgt] by lia.
      * exact Hle.
      * assert (x > 0) by nia.
        assert (x < 2) by nia.
        assert (x = 1) by lia.
        subst x.
        lia.
Qed.
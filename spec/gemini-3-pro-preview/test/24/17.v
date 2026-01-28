Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_234: largest_divisor_spec 234 117.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 2. reflexivity.
  - split.
    + lia.
    + intros k [x Hx] Hlt.
      destruct (Z_le_gt_dec k 0).
      * lia.
      * assert (x * k = 234) by lia.
        assert (x > 1) by nia.
        nia.
Qed.
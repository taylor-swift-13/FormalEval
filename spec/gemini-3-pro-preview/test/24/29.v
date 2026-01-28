Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_76: largest_divisor_spec 76 38.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 2. reflexivity.
  - split.
    + lia.
    + intros k [x Hx] Hlt.
      assert (k <= 0 \/ k > 0) as Hsign by lia.
      destruct Hsign as [Hneg | Hpos].
      * lia.
      * assert (x > 0) by nia.
        assert (x <> 1).
        { intro Heq. subst. lia. }
        assert (x >= 2) by lia.
        nia.
Qed.
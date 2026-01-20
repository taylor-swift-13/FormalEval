Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example largest_divisor_spec_3 : largest_divisor_spec 3%Z 1%Z.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 3%Z. lia.
  - right.
    split; [lia|].
    split; [lia|].
    intros m Hm Hdiv.
    destruct Hm as [Hm1 Hm2].
    destruct Hdiv as [k Hk].
    destruct (Z_lt_ge_dec m 2) as [Hm_lt2 | Hm_ge2].
    + assert (m = 1%Z) by lia. subst m. lia.
    + assert (m = 2%Z) by lia. subst m.
      exfalso.
      (* From Hk: 3 = 2 * k, derive a contradiction *)
      assert (k <= 0 \/ 1 <= k) by lia.
      destruct H as [Hk_le0 | Hk_ge1].
      * assert (2*k <= 0) by lia. lia.
      * destruct (Z_lt_ge_dec k 2) as [Hk_lt2 | Hk_ge2].
        -- assert (k = 1%Z) by lia. subst k. lia.
        -- assert (2*k >= 4) by lia. lia.
Qed.
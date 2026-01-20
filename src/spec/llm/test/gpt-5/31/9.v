Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_17 : is_prime_pred 17.
Proof.
  unfold is_prime_pred.
  split.
  - lia.
  - intros i [Hlow Hup] Hdiv.
    assert (Hsqrt : Z.sqrt 17 = 4) by (vm_compute; reflexivity).
    assert (Hi4 : i <= 4) by (rewrite Hsqrt in Hup; exact Hup).
    destruct (Z.eq_dec i 2) as [Hi2 | Hneq2].
    + subst i. unfold divides in Hdiv. destruct Hdiv as [k Hk].
      destruct (Z_le_gt_dec k 8) as [Hk_le | Hk_gt].
      * assert (Hle : 2 * k <= 16) by lia.
        rewrite <- Hk in Hle. lia.
      * assert (Hge : 18 <= 2 * k) by lia.
        rewrite <- Hk in Hge. lia.
    + assert (Hgt2 : 2 < i) by lia.
      destruct (Z.eq_dec i 3) as [Hi3 | Hneq3].
      * subst i. unfold divides in Hdiv. destruct Hdiv as [k Hk].
        destruct (Z_le_gt_dec k 5) as [Hk_le | Hk_gt].
        -- assert (Hle : 3 * k <= 15) by lia.
           rewrite <- Hk in Hle. lia.
        -- assert (Hge : 18 <= 3 * k) by lia.
           rewrite <- Hk in Hge. lia.
      * assert (Hgt3 : 3 < i) by lia.
        assert (Hi4eq : i = 4) by lia.
        subst i. unfold divides in Hdiv. destruct Hdiv as [k Hk].
        destruct (Z_le_gt_dec k 4) as [Hk_le | Hk_gt].
        -- assert (Hle : 4 * k <= 16) by lia.
           rewrite <- Hk in Hle. lia.
        -- assert (Hge : 20 <= 4 * k) by lia.
           rewrite <- Hk in Hge. lia.
Qed.

Example is_prime_spec_test_17 :
  is_prime_spec 17 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_17.
    + reflexivity.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply H. apply is_prime_17.
Qed.
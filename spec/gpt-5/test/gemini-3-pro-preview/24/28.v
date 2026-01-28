Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 99 33.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 3. reflexivity.
  - right.
    split.
    + lia.
    + split.
      * lia.
      * intros m H_range H_div.
        destruct H_div as [k Hk].
        assert (Hk_eq: k * m = 99) by (rewrite Hk; ring).
        assert (Hk_gt_1: k > 1).
        {
          destruct (Z_le_gt_dec k 1); [|assumption].
          assert (k * m <= 1 * m) by (apply Z.mul_le_mono_nonneg_r; lia).
          lia.
        }
        assert (Hk_neq_2: k <> 2).
        {
          intro Hk2; subst k.
          assert (Hdiv2: Z.divide 2 99). { exists m. rewrite Hk. ring. }
          apply Z.mod_divide in Hdiv2; [|lia].
          vm_compute in Hdiv2. discriminate.
        }
        assert (Hk_ge_3: k >= 3) by lia.
        assert (3 * m <= 99).
        {
          rewrite <- Hk_eq.
          apply Z.mul_le_mono_nonneg_r; lia.
        }
        lia.
Qed.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example largest_divisor_spec_29 : largest_divisor_spec 29%Z 1%Z.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 29%Z. lia.
  - right.
    split; [lia|].
    split; [lia|].
    intros m Hm Hdiv.
    destruct Hm as [Hm1 Hm2].
    destruct Hdiv as [k Hk].
    destruct (Z_lt_ge_dec m 2) as [Hm_lt2 | Hm_ge2].
    + assert (m = 1%Z) by lia. subst m. lia.
    + destruct (Z_lt_ge_dec m 15) as [Hm_lt15 | Hm_ge15].
      * destruct (Z_lt_ge_dec m 3) as [Hm_lt3 | Hm_ge3].
        -- assert (m = 2%Z) by lia. subst m. exfalso. lia.
        -- destruct (Z_lt_ge_dec m 4) as [Hm_lt4 | Hm_ge4].
           --- assert (m = 3%Z) by lia. subst m. exfalso. lia.
           --- destruct (Z_lt_ge_dec m 5) as [Hm_lt5 | Hm_ge5].
               ---- assert (m = 4%Z) by lia. subst m. exfalso. lia.
               ---- destruct (Z_lt_ge_dec m 6) as [Hm_lt6 | Hm_ge6].
                    ----- assert (m = 5%Z) by lia. subst m. exfalso. lia.
                    ----- destruct (Z_lt_ge_dec m 7) as [Hm_lt7 | Hm_ge7].
                          ------ assert (m = 6%Z) by lia. subst m. exfalso. lia.
                          ------ destruct (Z_lt_ge_dec m 8) as [Hm_lt8 | Hm_ge8].
                                  ------- assert (m = 7%Z) by lia. subst m. exfalso. lia.
                                  ------- destruct (Z_lt_ge_dec m 9) as [Hm_lt9 | Hm_ge9].
                                          -------- assert (m = 8%Z) by lia. subst m. exfalso. lia.
                                          -------- destruct (Z_lt_ge_dec m 10) as [Hm_lt10 | Hm_ge10].
                                                   --------- assert (m = 9%Z) by lia. subst m. exfalso. lia.
                                                   --------- destruct (Z_lt_ge_dec m 11) as [Hm_lt11 | Hm_ge11].
                                                            ---------- assert (m = 10%Z) by lia. subst m. exfalso. lia.
                                                            ---------- destruct (Z_lt_ge_dec m 12) as [Hm_lt12 | Hm_ge12].
                                                                         ----------- assert (m = 11%Z) by lia. subst m. exfalso. lia.
                                                                         ----------- destruct (Z_lt_ge_dec m 13) as [Hm_lt13 | Hm_ge13].
                                                                                      ------------ assert (m = 12%Z) by lia. subst m. exfalso. lia.
                                                                                      ------------ destruct (Z_lt_ge_dec m 14) as [Hm_lt14 | Hm_ge14].
                                                                                                    ------------- assert (m = 13%Z) by lia. subst m. exfalso. lia.
                                                                                                    ------------- assert (m = 14%Z) by lia. subst m. exfalso. lia.
      * exfalso.
        assert (k >= 1) by lia.
        assert (k <= 1) by lia.
        assert (k = 1) by lia.
        subst k.
        lia.
Qed.
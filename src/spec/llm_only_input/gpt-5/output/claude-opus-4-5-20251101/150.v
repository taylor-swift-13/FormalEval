Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma is_prime_7 : is_prime 7%Z.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd Hdd.
    destruct (Z_le_gt_dec d 2) as [Hle|Hgt].
    + assert (d = 2) by lia. subst d.
      vm_compute. discriminate.
    + exfalso.
      set (m := d - 3).
      assert (Hm : 0 <= m) by lia.
      replace d with (3 + m) in Hdd by lia.
      assert (Hge9: 9 <= (3 + m) * (3 + m)).
      {
        rewrite Z.mul_add_distr_r.
        rewrite Z.mul_add_distr_l.
        rewrite Z.mul_add_distr_l.
        (* (3 + m) * (3 + m) = 9 + 3*m + m*3 + m*m *)
        assert (H3m1 : 0 <= 3 * m) by (apply Z.mul_nonneg_nonneg; lia).
        assert (H3m2 : 0 <= m * 3) by (apply Z.mul_nonneg_nonneg; lia).
        assert (Hm2  : 0 <= m * m) by (apply Z.mul_nonneg_nonneg; lia).
        assert (Hsum1 : 0 <= 3 * m + m * 3) by (apply Z.add_nonneg_nonneg; assumption).
        assert (Hsum2 : 0 <= 3 * m + m * 3 + m * m) by (apply Z.add_nonneg_nonneg; assumption || assumption).
        lia.
      }
      lia.
Qed.

Example x_or_y_spec_test_7_34_12 : x_or_y_spec 7%Z 34%Z 12%Z 34%Z.
Proof.
  unfold x_or_y_spec.
  split.
  - intros _. reflexivity.
  - intros H. exfalso. apply H. apply is_prime_7.
Qed.
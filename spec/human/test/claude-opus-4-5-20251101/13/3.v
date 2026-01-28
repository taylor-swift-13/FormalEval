Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_13_pre (a b : Z) : Prop :=
  a <> 0 \/ b <> 0.

Definition problem_13_spec_gcd (a b output : Z) : Prop :=
  (a mod output = 0) /\
  (b mod output = 0) /\
  (forall x : Z, (a mod x = 0) -> (b mod x = 0) -> x > 0 -> x <= output).

Definition problem_13_spec (a b output : Z) : Prop :=
  (output mod a = 0) /\
  (output mod b = 0) /\
  (forall x : Z, (x mod a = 0) -> (x mod b = 0) -> x > 0 -> x <= output).

Example test_problem_13 : problem_13_spec_gcd 49 14 7.
Proof.
  unfold problem_13_spec_gcd.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros x H49 H14 Hpos.
      apply Z.mod_divide in H49; [|lia].
      apply Z.mod_divide in H14; [|lia].
      destruct H49 as [k49 Hk49].
      destruct H14 as [k14 Hk14].
      assert (Hx_le_14: x <= 14).
      {
        assert (k14 > 0 \/ k14 = 0 \/ k14 < 0) by lia.
        destruct H as [Hkpos | [Hk0 | Hkneg]].
        - destruct (Z_le_dec x 14); auto.
          assert (x >= 15) by lia.
          assert (k14 * x >= 15) by lia.
          lia.
        - subst k14. lia.
        - assert (k14 * x <= -1 * 1) by lia.
          lia.
      }
      destruct (Z.eq_dec x 1); [lia|].
      destruct (Z.eq_dec x 2).
      {
        subst x. compute in Hk49. lia.
      }
      destruct (Z.eq_dec x 3).
      {
        subst x. 
        assert (3 * k49 = 49) by lia.
        assert (49 = 3 * 16 + 1) by lia.
        lia.
      }
      destruct (Z.eq_dec x 4).
      {
        subst x. compute in Hk49. lia.
      }
      destruct (Z.eq_dec x 5).
      {
        subst x.
        assert (5 * k49 = 49) by lia.
        assert (49 = 5 * 9 + 4) by lia.
        lia.
      }
      destruct (Z.eq_dec x 6).
      {
        subst x.
        assert (6 * k49 = 49) by lia.
        assert (49 = 6 * 8 + 1) by lia.
        lia.
      }
      destruct (Z.eq_dec x 7); [lia|].
      destruct (Z.eq_dec x 8).
      {
        subst x.
        assert (8 * k14 = 14) by lia.
        lia.
      }
      destruct (Z.eq_dec x 9).
      {
        subst x.
        assert (9 * k14 = 14) by lia.
        lia.
      }
      destruct (Z.eq_dec x 10).
      {
        subst x.
        assert (10 * k14 = 14) by lia.
        lia.
      }
      destruct (Z.eq_dec x 11).
      {
        subst x.
        assert (11 * k14 = 14) by lia.
        lia.
      }
      destruct (Z.eq_dec x 12).
      {
        subst x.
        assert (12 * k14 = 14) by lia.
        lia.
      }
      destruct (Z.eq_dec x 13).
      {
        subst x.
        assert (13 * k14 = 14) by lia.
        lia.
      }
      destruct (Z.eq_dec x 14).
      {
        subst x.
        assert (14 * k49 = 49) by lia.
        assert (49 = 14 * 3 + 7) by lia.
        lia.
      }
      lia.
Qed.
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

Example test_problem_13 : problem_13_spec_gcd 14 540 2.
Proof.
  unfold problem_13_spec_gcd.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros x H14 H540 Hpos.
      assert (Hx_le_14: x <= 14).
      {
        apply Z.mod_divide in H14; [|lia].
        destruct H14 as [k Hk].
        assert (k > 0 \/ k = 0 \/ k < 0) by lia.
        destruct H as [Hkpos | [Hk0 | Hkneg]].
        - destruct (Z_le_dec x 14); auto.
          assert (x >= 15) by lia.
          assert (k >= 1) by lia.
          assert (k * x >= 15) by lia.
          lia.
        - subst k. lia.
        - assert (k * x <= -1 * 1) by lia.
          lia.
      }
      destruct (Z.eq_dec x 1); [lia|].
      destruct (Z.eq_dec x 2); [lia|].
      destruct (Z.eq_dec x 3).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 4).
      {
        subst x. compute in H540. discriminate.
      }
      destruct (Z.eq_dec x 5).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 6).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 7).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 8).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 9).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 10).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 11).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 12).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 13).
      {
        subst x. compute in H14. discriminate.
      }
      destruct (Z.eq_dec x 14).
      {
        subst x. compute in H540. discriminate.
      }
      lia.
Qed.
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

Example test_problem_13 : problem_13_spec_gcd 21 35 7.
Proof.
  unfold problem_13_spec_gcd.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros x H21 H35 Hpos.
      assert (Hx_div_21: (x | 21)).
      {
        apply Z.mod_divide; [lia | exact H21].
      }
      assert (Hx_div_35: (x | 35)).
      {
        apply Z.mod_divide; [lia | exact H35].
      }
      destruct Hx_div_21 as [k21 Hk21].
      destruct Hx_div_35 as [k35 Hk35].
      assert (Hx_le_21: x <= 21).
      {
        assert (k21 > 0 \/ k21 = 0 \/ k21 < 0) by lia.
        destruct H as [Hkpos | [Hk0 | Hkneg]].
        - destruct (Z_le_dec x 21); auto.
          assert (x >= 22) by lia.
          assert (k21 * x >= 22) by lia.
          lia.
        - subst k21. lia.
        - assert (k21 * x <= -1 * 1) by lia.
          lia.
      }
      destruct (Z.eq_dec x 1); [lia|].
      destruct (Z.eq_dec x 2).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 3).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 4).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 5).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 6).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 7); [lia|].
      destruct (Z.eq_dec x 8).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 9).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 10).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 11).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 12).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 13).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 14).
      { subst x. compute in H35. discriminate. }
      destruct (Z.eq_dec x 15).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 16).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 17).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 18).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 19).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 20).
      { subst x. compute in H21. discriminate. }
      destruct (Z.eq_dec x 21).
      { subst x. compute in H35. discriminate. }
      lia.
Qed.
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

Example test_problem_13 : problem_13_spec_gcd 81 80 1.
Proof.
  unfold problem_13_spec_gcd.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros x H81 H80 Hpos.
      assert (Hx_le_81: x <= 81).
      {
        apply Z.mod_divide in H81; [|lia].
        destruct H81 as [k Hk].
        assert (k > 0 \/ k = 0 \/ k < 0) by lia.
        destruct H as [Hkpos | [Hk0 | Hkneg]].
        - destruct (Z_le_dec x 81); auto.
          assert (x >= 82) by lia.
          assert (k >= 1) by lia.
          assert (k * x >= 82) by lia.
          lia.
        - subst k. lia.
        - assert (k * x <= -1 * 1) by lia.
          lia.
      }
      assert (Hx_le_80: x <= 80).
      {
        apply Z.mod_divide in H80; [|lia].
        destruct H80 as [k Hk].
        assert (k > 0 \/ k = 0 \/ k < 0) by lia.
        destruct H as [Hkpos | [Hk0 | Hkneg]].
        - destruct (Z_le_dec x 80); auto.
          assert (x >= 81) by lia.
          assert (k >= 1) by lia.
          assert (k * x >= 81) by lia.
          lia.
        - subst k. lia.
        - assert (k * x <= -1 * 1) by lia.
          lia.
      }
      destruct (Z.eq_dec x 1); [lia|].
      destruct (Z.eq_dec x 2).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 3).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 4).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 5).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 6).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 7).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 8).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 9).
      { subst x. compute in H80. discriminate. }
      destruct (Z.eq_dec x 10).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 16).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 20).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 27).
      { subst x. compute in H80. discriminate. }
      destruct (Z.eq_dec x 40).
      { subst x. compute in H81. discriminate. }
      destruct (Z.eq_dec x 80).
      { subst x. compute in H81. discriminate. }
      assert (x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ 
              x = 17 \/ x = 18 \/ x = 19 \/ x = 21 \/ x = 22 \/ 
              x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 28 \/ 
              x = 29 \/ x = 30 \/ x = 31 \/ x = 32 \/ x = 33 \/
              x = 34 \/ x = 35 \/ x = 36 \/ x = 37 \/ x = 38 \/
              x = 39 \/ x = 41 \/ x = 42 \/ x = 43 \/ x = 44 \/
              x = 45 \/ x = 46 \/ x = 47 \/ x = 48 \/ x = 49 \/
              x = 50 \/ x = 51 \/ x = 52 \/ x = 53 \/ x = 54 \/
              x = 55 \/ x = 56 \/ x = 57 \/ x = 58 \/ x = 59 \/
              x = 60 \/ x = 61 \/ x = 62 \/ x = 63 \/ x = 64 \/
              x = 65 \/ x = 66 \/ x = 67 \/ x = 68 \/ x = 69 \/
              x = 70 \/ x = 71 \/ x = 72 \/ x = 73 \/ x = 74 \/
              x = 75 \/ x = 76 \/ x = 77 \/ x = 78 \/ x = 79 \/
              x = 81) by lia.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      subst x; compute in H81; try discriminate; compute in H80; try discriminate.
Qed.
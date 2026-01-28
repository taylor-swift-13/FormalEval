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

Example test_problem_13 : problem_13_spec_gcd 14 28 14.
Proof.
  unfold problem_13_spec_gcd.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros x H14 H28 Hpos.
      apply Z.mod_divide in H14; [|lia].
      apply Z.mod_divide in H28; [|lia].
      destruct H14 as [k1 Hk1].
      destruct H28 as [k2 Hk2].
      assert (k1 > 0 \/ k1 = 0 \/ k1 < 0) by lia.
      destruct H as [Hk1pos | [Hk10 | Hk1neg]].
      * destruct (Z_le_dec x 14); auto.
        assert (x >= 15) by lia.
        assert (k1 * x >= 15) by lia.
        lia.
      * subst k1. lia.
      * assert (k1 * x <= -1 * 1) by lia.
        lia.
Qed.
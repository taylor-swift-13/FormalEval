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

Example test_problem_13 : problem_13_spec_gcd 100 50 50.
Proof.
  unfold problem_13_spec_gcd.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros x H100 H50 Hpos.
      apply Z.mod_divide in H50; [|lia].
      destruct H50 as [k Hk].
      assert (k > 0 \/ k = 0 \/ k < 0) by lia.
      destruct H as [Hkpos | [Hk0 | Hkneg]].
      * destruct (Z_le_dec x 50); auto.
        assert (x >= 51) by lia.
        assert (k = 1) by lia.
        subst k. lia.
      * subst k. lia.
      * assert (k * x <= -1 * 1) by lia.
        lia.
Qed.
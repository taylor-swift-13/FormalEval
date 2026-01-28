Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Example test_case_1 : problem_75_spec 5%Z false.
Proof.
  unfold problem_75_spec.
  split.
  - intros H.
    exfalso.
    destruct H as [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Ha]]]]]].
    assert (Hprod : p1 * p2 * p3 = 5) by assumption.
    assert (Hp1_ge_2 : p1 >= 2) by (apply prime_ge_2; assumption).
    assert (Hp2_ge_2 : p2 >= 2) by (apply prime_ge_2; assumption).
    assert (Hp3_ge_2 : p3 >= 2) by (apply prime_ge_2; assumption).
    assert (Hpos : p1 * p2 * p3 >= 2 * 2 * 2).
    { apply Zmult_ge_compat; try lia. }
    lia.
  - intros H.
    reflexivity.
Qed.
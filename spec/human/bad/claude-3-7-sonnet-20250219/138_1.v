Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Example test_case_4_false :
  problem_138_spec 4 false.
Proof.
  unfold problem_138_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Heq]]]]]]]]].
    unfold is_positive_even in *.
    destruct H1 as [k1 [He1 Hk1]].
    destruct H2 as [k2 [He2 Hk2]].
    destruct H3 as [k3 [He3 Hk3]].
    destruct H4 as [k4 [He4 Hk4]].
    rewrite He1, He2, He3, He4 in Heq.
    rewrite <- !Z.mul_add_distr_l in Heq.
    set (K := k1 + k2 + k3 + k4) in *.
    assert (K_ge_4 : (K >= 4)%Z). {
      unfold K. lia.
    }
    assert (K_eq_2 : K = 2). {
      apply (Z.mul_eq_reg_r 2 4 K).
      lia.
      lia.
      lia.
      exact Heq.
    }
    lia.
Qed.
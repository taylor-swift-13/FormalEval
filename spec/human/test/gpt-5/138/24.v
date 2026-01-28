Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition problem_138_pre (n : Z) : Prop := True.

Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Example problem_138_test_case_0 :
  problem_138_spec 35%Z false.
Proof.
  unfold problem_138_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hex.
    destruct Hex as [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Hsum]]]]]]]].
    destruct H1 as [k1 [He1 Hk1pos]].
    destruct H2 as [k2 [He2 Hk2pos]].
    destruct H3 as [k3 [He3 Hk3pos]].
    destruct H4 as [k4 [He4 Hk4pos]].
    subst e1 e2 e3 e4.
    exfalso.
    lia.
Qed.
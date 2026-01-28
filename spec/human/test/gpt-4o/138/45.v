Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

(* Definition of positive even number *)
Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

(* Arbitrary integer n *)
Definition problem_138_pre (n : Z) : Prop := True.

(* Specification: true if and only if there exist four positive even numbers whose sum equals n *)
Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

(* Test case for input 105, expected output false *)
Example test_case_105 : problem_138_spec 105 false.
Proof.
  unfold problem_138_spec.
  split.
  - intros H. discriminate H.
  - intros [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Heq]]]]]]]].
    destruct H1 as [k1 [He1 Hk1]].
    destruct H2 as [k2 [He2 Hk2]].
    destruct H3 as [k3 [He3 Hk3]].
    destruct H4 as [k4 [He4 Hk4]].
    rewrite He1, He2, He3, He4 in Heq.
    assert (105 <= 2 * k1 + 2 * k2 + 2 * k3 + 2 * k4) by lia.
    assert ((2 * k1 + 2 * k2 + 2 * k3 + 2 * k4) mod 2 = 0) by (rewrite Z.add_mod; lia).
    assert (105 mod 2 = 1) by lia.
    lia.
Qed.
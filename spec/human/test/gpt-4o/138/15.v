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

Example test_case_42 : problem_138_spec 42 true.
Proof.
  unfold problem_138_spec.
  split.
  - intros _. exists 2, 4, 10, 26.
    split; [exists 1; lia |].
    split; [exists 2; lia |].
    split; [exists 5; lia |].
    split; [exists 13; lia |].
    lia.
  - intros [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Heq]]]]]]]].
    destruct H1 as [k1 [He1 Hk1]].
    destruct H2 as [k2 [He2 Hk2]].
    destruct H3 as [k3 [He3 Hk3]].
    destruct H4 as [k4 [He4 Hk4]].
    rewrite He1, He2, He3, He4 in Heq.
    assert (42 = 2 * k1 + 2 * k2 + 2 * k3 + 2 * k4) by lia.
    assert (k1 > 0 /\ k2 > 0 /\ k3 > 0 /\ k4 > 0) by lia.
    reflexivity.
Qed.
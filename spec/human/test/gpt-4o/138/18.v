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

Example test_case_28 : problem_138_spec 28 true.
Proof.
  unfold problem_138_spec.
  split.
  - intros. exists 8, 6, 10, 4.
    split; [exists 4; split; lia|].
    split; [exists 3; split; lia|].
    split; [exists 5; split; lia|].
    split; [exists 2; split; lia|].
    lia.
  - intros [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Heq]]]]]]]].
    destruct H1 as [k1 [He1 Hk1]].
    destruct H2 as [k2 [He2 Hk2]].
    destruct H3 as [k3 [He3 Hk3]].
    destruct H4 as [k4 [He4 Hk4]].
    rewrite He1, He2, He3, He4 in Heq.
    assert (28 = 2 * k1 + 2 * k2 + 2 * k3 + 2 * k4) by lia.
    reflexivity.
Qed.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition is_equal_to_sum_even_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Lemma test_case_proof : is_equal_to_sum_even_spec 4 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intro H. discriminate H.
  - intro H.
    destruct H as [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 H5]]]]]]]].
    unfold is_positive_even in H1, H2, H3, H4.
    destruct H1 as [k1 [H1a H1b]].
    destruct H2 as [k2 [H2a H2b]].
    destruct H3 as [k3 [H3a H3b]].
    destruct H4 as [k4 [H4a H4b]].
    rewrite H1a, H2a, H3a, H4a in H5.
    replace (2 * k1 + 2 * k2 + 2 * k3 + 2 * k4) with (2 * (k1 + k2 + k3 + k4)) in H5 by lia.
    assert (k1 + k2 + k3 + k4 > 0) by lia.
    nia.
Qed.